#![feature(drain_filter, array_windows, iter_collect_into)]

use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::HashSet;
use std::collections::HashMap;
use std::iter::Peekable;
use std::marker::PhantomData;
use std::ops::Deref;
use std::str::Chars;
use either::Either;
use multimap::MultiMap;

struct First<Tok> {
    nullable: bool,
    toks: HashSet<Tok>,
}

struct Production<Nt, Tok> {
    lhs: Nt,
    rhs: Vec<RuleStr<Nt, Tok>>
}

#[derive(Debug)]
struct Grammar<Nt, Tok> {
    productions: HashMap<Nt, Vec<RuleStr<Nt, Tok>>>
}

impl<Nt, Tok> FromIterator<Production<Nt, Tok>> for Grammar<Nt, Tok>
where Nt: Eq+Hash
{
    fn from_iter<T>(iter: T) -> Self 
    where T: IntoIterator<Item = Production<Nt, Tok>>
    {
        Grammar { 
            productions: iter.into_iter()
                .map(|p| (p.lhs, p.rhs))
                .collect()
        }
    }
}

trait Inexhaustible {
    fn new_unused<'a>(used: impl Iterator<Item = &'a Self>) -> Self
    where Self: 'a;
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuleStr<Nt, Tok> (Vec<Either<Nt, Tok>>);

impl<Nt, Tok> Deref for RuleStr<Nt, Tok> {
    type Target = [Either<Nt, Tok>];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<Nt, Tok> IntoIterator for RuleStr<Nt, Tok> {
    type Item = Either<Nt, Tok>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<Nt, Tok> RuleStr<Nt, Tok> {
    fn transform_toks<NTok, F>(self, f: F) -> RuleStr<Nt, NTok>
    where F: Fn(Tok) -> NTok 
    {
        RuleStr(self.into_iter().map(|e| e.map_right(&f)).collect())
    }
}

#[derive(Debug)]
struct ParserEntry<Nt, Tok> {
    first: HashMap<Option<Tok>, RuleStr<Nt, Tok>>,
    follow: HashSet<Tok>
}

impl<Nt, Tok> Default for ParserEntry<Nt, Tok> {
    fn default() -> Self {
        Self { first: Default::default(), follow: Default::default() }
    }
}

impl<Nt: PartialEq, Tok: Eq+Hash> PartialEq for ParserEntry<Nt, Tok> {
    fn eq(&self, other: &Self) -> bool {
        self.first == other.first && self.follow == other.follow
    }
}

impl<Nt: Eq, Tok: Eq+Hash> Eq for ParserEntry<Nt, Tok> {
    fn assert_receiver_is_total_eq(&self) {}
}

struct Parser<Nt, Tok> {
    entries: HashMap<Nt, ParserEntry<Nt, Tok>>
}

impl<Nt, Tok> Grammar<Nt, Tok>
where
    Nt: Eq+Copy+Hash+Inexhaustible+Debug,
    Tok: Eq+Copy+Hash+Debug,
{
    pub fn transform_left_rec(&mut self)
    {
        // incomplete
        let mut nts = self.productions.keys().map(|nt| *nt).collect::<HashSet<_>>();

        while let Some(nt) = nts.iter().next() {
            self.transform_left_rec_scc(*nt, &mut nts);
        }
    }

    fn transform_left_rec_scc(&mut self, start: Nt, unvisited: &mut HashSet<Nt>)
    {
        let mut stack = vec![start];

        while let Some(curr) = stack.pop() {
            let reach: Vec<_> = self.productions
                .get(&curr).unwrap().iter().enumerate()
                .filter_map(|(idx, rhs)| { match rhs.get(0) {
                    Some(Either::Left(nt)) => Some((*nt, idx)),
                    _ => None
                }}).collect();

            let mut new_rules = Vec::new();
            for (nt, index) in reach {
                if unvisited.contains(&nt) {
                    eprintln!("connection: {:?} -> {:?}", curr, nt);
                    stack.push(nt);
                }
                else {
                    eprintln!("loop detected: {:?} -> {:?}", curr, nt);
                    let rhs = self.productions.get_mut(&curr).unwrap().remove(index);
                    new_rules.extend(self.expand_rhs(curr, rhs, &unvisited).into_iter());
                }
            }

            self.productions.get_mut(&curr).unwrap().append(&mut new_rules);
            self.cut_left_rec(curr);
            unvisited.remove(&curr);
        }
    }

    fn expand_rhs(&self, lhs: Nt, rhs: RuleStr<Nt, Tok>, unvisited: &HashSet<Nt>) -> Vec<RuleStr<Nt, Tok>>
    {
        let should_expand = |it: Either<Nt, Tok>| -> bool {
            ! it.is_right() 
                && lhs != it.unwrap_left() 
                && ! unvisited.contains(&it.unwrap_left())            
        };

        let mut result: Vec<RuleStr<_, _>> = Vec::new();
        let mut queue: VecDeque<RuleStr<_, _>> = VecDeque::from([rhs]);

        while let Some(unproc) = queue.pop_front() {
            if should_expand(unproc[0]) {
                self.productions.get(&unproc[0].unwrap_left()).unwrap().iter()
                    .map(|ins|{
                        eprintln!("Expanding {:?} inside {:?}", unproc[0], lhs);
                        let mut res = ins.clone();
                        res.0.extend_from_slice(&unproc[1..]);
                        res
                    })
                    .collect_into(&mut queue);
            }
            else {
                result.push(unproc);
            }
        }

        result
    }

    fn cut_left_rec(&mut self, sym: Nt)
    {
        let new_nt = Nt::new_unused(self.productions.keys());
        
        let cases = self.productions
            .get_mut(&sym)
            .unwrap();

        let mut rec_cases = cases.drain_filter(|c| {
            c.starts_with(&vec![Either::Left(sym)])
        }).collect::<Vec<_>>();

        if rec_cases.len() == 0 { return }
        eprintln!("Cutting self-loops on {:?}", sym);

        for case in rec_cases.iter_mut() {
            case.0.remove(0);
            case.0.push(Either::Left(new_nt));
        }

        rec_cases.push(RuleStr(vec![]));

        for case in cases.iter_mut() {
            case.0.push(Either::Left(new_nt));
        }
        drop(cases);
        
        self.productions.insert(new_nt, rec_cases);
    }

}

impl<Nt, Tok> Grammar<Nt, Tok>
where
    Nt: Eq+Hash+Debug+Copy,
    Tok: Eq+Hash+Debug+Copy
{
    fn first<'a>(&'a self, mut alpha: impl Iterator<Item = &'a Either<Nt, Tok>>) -> First<Tok>
    {
        let mut res = HashSet::new();

        while let Some(first) = alpha.next() {
            if first.is_right() {
                res.insert(first.unwrap_right());
                return First { 
                    nullable: false,
                    toks: res
                };   
            }

            let ruls = self.productions.get(&first.unwrap_left());
            let mut nullable = false;

            for rul in ruls.iter().map(|v| v.iter()).flatten() {
                let inner = self.first(rul.iter());
                nullable |= inner.nullable;
                res.extend(inner.toks.iter());
            }

            if ! nullable {
                return First {
                    nullable: false,
                    toks: res
                }
            }
        }

        First { nullable: true, toks: res }
    }

    fn follow_map(&self) -> HashMap<Nt, HashSet<Tok>>
    {
        let mut follow_paths: MultiMap<Nt, Nt> = MultiMap::new();
        let mut res: HashMap<Nt, HashSet<Tok>> = HashMap::new();

        for (lhs, ruls) in &self.productions {
            res.entry(*lhs).or_default();

            for rhs in ruls {
                rhs.iter().rev()
                    .scan(VecDeque::new(), |suffix, sym| {
                        suffix.push_front(sym); 
                        Some(suffix.clone())
                    })
                    .flat_map(|mut alpha| {
                        if let Some(Either::Left(nt)) = alpha.pop_front() {
                            let fst = self.first(alpha.into_iter());
                            res.entry(*nt).or_default().extend(fst.toks.iter());

                            if fst.nullable && *nt != *lhs {
                                return Some((*nt, *lhs))
                            }
                        }

                        None::<(Nt, Nt)>
                    })
                    .collect_into(&mut follow_paths);
            }
        }

        loop {
            let mut changed = false;

            for (fst, snd) in &follow_paths {
                for nt in snd {
                    let toks: Vec<Tok> = res.get(nt).iter()
                        .flat_map(|l| l.iter().map(|t| *t))
                        .collect();

                    for tok in toks {
                        changed |= res.entry(*fst).or_default().insert(tok);                        
                    }
                }
            }

            if ! changed { break res; }
        }
    }
}

impl<Nt, Tok> From<&Grammar<Nt, Tok>> for Parser<Nt, Tok>
where
    Tok: Eq+Hash+Debug+Copy,
    Nt: Eq+Hash+Copy+Debug
{
    fn from(value: &Grammar<Nt, Tok>) -> Self {
        let mut entries: HashMap<Nt, ParserEntry<Nt, Tok>> = HashMap::new();

        let mut follow_map = value.follow_map();

        for (&lhs, ruls) in &value.productions {
            for rhs in ruls {
                let fst = value.first(rhs.iter());
                let entry = entries.entry(lhs).or_default();

                if fst.nullable {
                    entry.first.insert(None, rhs.clone());
                }

                for &tok in &fst.toks {
                    entry.first.insert(Some(tok), rhs.clone());
                }

                follow_map.remove(&lhs)
                    .unwrap_or_default()
                    .into_iter().collect_into(&mut entry.follow);
            }
        }

        Parser { entries }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
enum ParseTree<Nt, Tok> {
    Leaf(Tok),
    Node {
        label: Nt,
        children: Vec<ParseTree<Nt, Tok>>
    }
}

trait TokenStream: Iterator
where
    Self::Label: Label<Self::Item>
{
    type Label;

    fn peek_label(&mut self) -> Option<Self::Label>;
}

trait Label<T>: Eq+Hash+Copy {
    fn get_label(value: &T) -> Self;
}

impl<T: Copy+Eq+Hash> Label<T> for T {
    fn get_label(value: &T) -> Self {
        *value
    }
}

trait IntoTokenStream<L>
where
    L: Label<Self::Item>,
    Self::IntoTokenStream: TokenStream<Label = L, Item = Self::Item>,
{
    type Item;
    type IntoTokenStream;

    fn into_token_stream(self) -> Self::IntoTokenStream;
}

struct LabeldStream<T, L> {
    inner: Peekable<std::vec::IntoIter<T>>,
    phantom: PhantomData<L>
}

impl<T, L> Iterator for LabeldStream<T, L>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<T, L> TokenStream for LabeldStream<T, L>
where L: Label<T>
{
    type Label = L;

    fn peek_label(&mut self) -> Option<Self::Label> {
        self.inner.peek().map(|t| L::get_label(t))
    }
}

impl<T, L: Label<T>> IntoTokenStream<L> for Vec<T>
{
    type Item = T;

    type IntoTokenStream = LabeldStream<T, L>;

    fn into_token_stream(self) -> Self::IntoTokenStream {
        LabeldStream {
            inner: self.into_iter().peekable(),
            phantom: PhantomData {}
        }
    }
}

struct CharStream<T: Iterator<Item = char>>(Peekable<T>);

impl<'a> From<&'static str> for CharStream<Chars<'a>> {
    fn from(value: &'static str) -> Self {
        CharStream(value.chars().peekable())
    }
}

impl<T: Iterator<Item = char>> Iterator for CharStream<T> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<T: Iterator<Item = char>> TokenStream for CharStream<T> {
    type Label = char;

    fn peek_label(&mut self) -> Option<Self::Label> {
        self.0.peek().copied()
    }
}

impl<Nt, Tok> Parser<Nt, Tok> 
where
    Nt: Copy+Eq+Hash,
    Tok: Eq+Hash+Copy
{
    fn select_rule(&self, nt: Nt, inp: Option<Tok>) -> Option<&RuleStr<Nt, Tok>>
    {
        self.entries.get(&nt).and_then(|entry| {
            let em_rule = entry.first.get(&None);

            match inp {
                None => em_rule,
                Some(tok) => {
                    if entry.follow.contains(&tok) {
                        em_rule
                    }
                    else {
                        entry.first.get(&Some(tok))
                    }
                }
            }
        })
    }

    fn parse<T, I>(&self, stream: &mut T, start: Nt) -> Option<ParseTree<Nt, I>>
    where
        T: TokenStream<Label = Tok, Item = I>,
        Tok: Label<I>+Debug
    {
        let mut children = Vec::new();

        let curr_tok = stream.peek_label();
        let rule = self.select_rule(start, curr_tok)?;

        for it in rule.0.iter() {
            match it {
                Either::Left(nt) => {
                    let subt = self.parse(stream, *nt)?;
                    children.push(subt);
                },
                Either::Right(st) => {
                    let tok = stream.next().unwrap();
                    assert_eq!(Tok::get_label(&tok), *st);
                    children.push(ParseTree::Leaf(tok));
                }
            }
        }

        Some(ParseTree::Node { label: start, children })
    }
}

#[cfg(test)]
macro_rules! char_prod_rhs {
    (<>) => { crate::RuleStr(vec![]) };
    (<$($sym:literal)+>) => {
        crate::RuleStr(vec![
            $(if $sym.is_uppercase() { either::Either::Left($sym) }
            else { either::Either::Right($sym) }),+
        ])
    };
}

#[cfg(test)]
macro_rules! char_prod_rule {
    ($lhs:expr => $(<$($rhs:literal)*>),+) => {
        crate::Production { lhs: $lhs, rhs: vec![ $( char_prod_rhs!(<$($rhs)*>) ),+ ] }
    };
}

#[cfg(test)]
macro_rules! grammar {
    ($($($rule:tt)+);*) => {
        [ $( $($rule)+ )* ].into_iter().collect::<Grammar<_,_>>()
    }
}

#[cfg(test)]
macro_rules! pt_node {
    ( $label:expr ; $($child:expr),* ) => {
        crate::ParseTree::Node {
            label: $label,
            children: vec! [ $($child),* ]
        }
    };
}

impl Inexhaustible for char {
    fn new_unused<'a>(used: impl Iterator<Item = &'a Self>) -> Self
    where Self: 'a {
        let m = *used.max().unwrap_or(&'A');

        char::try_from(Into::<u32>::into(m) + 1).expect("failed to create fresh symbol")
    }
}

#[cfg(test)]
mod test {
    use either::Either;
    use std::{collections::{HashMap, HashSet}};
    use crate::{ParserEntry, ParseTree, Parser, CharStream, IntoTokenStream, Label};

    use super::Grammar;

    #[test]
    fn transform_simple()
    {
        // E -> Ea | b
        // ==>
        // E -> bT
        // T -> epsilon | aT

        let mut g = grammar! {
            char_prod_rule! { 'E' => <'b'>, <'E''a'> }
        };

        let target = grammar! {
            char_prod_rule! { 'E' => <'b''F'> },
            char_prod_rule! { 'F' => <'a''F'>, <> }
        };

        // g.transform_left_rec_scc('E', &mut g.productions.keys().map(|c| *c).collect());
        g.transform_left_rec();

        assert_eq!(g.productions, target.productions);

        assert_eq!(g.productions.len(), 2);
        assert_eq!(g.productions.get(&'E').map(|v| v.len()), Some(1));

        let mod_rhs = g.productions[&'E'].get(0).unwrap();
        assert_eq!(mod_rhs.len(), 2);
        assert_eq!(mod_rhs.get(0), Some(&Either::Right('b')));

        let fresh = mod_rhs.get(1).unwrap().unwrap_left();
        let fresh_cases = g.productions.get(&fresh).unwrap();
        assert_eq!(fresh_cases.len(), 2);
    }

    #[test]
    fn transform_transitive()
    {
        let mut g = grammar! {
            char_prod_rule! { 'A' => <'x'>, <'B''a'> },
            char_prod_rule! { 'B' => <'C''b'> },
            char_prod_rule! { 'C' => <'A''c'> }
        };

        let target = grammar! {
            char_prod_rule! { 'A' => <'x'>, <'B''a'> },
            char_prod_rule! { 'B' => <'C''b'> },
            char_prod_rule! { 'C' => <'x''c''D'> },
            char_prod_rule! { 'D' => <'b''a''c''D'>, <> }
        };

        g.transform_left_rec_scc('A', &mut g.productions.keys().map(|c| *c).collect());

        assert_eq!(g.productions, target.productions);
    }

    #[test]
    fn simple_first()
    {
        let g = grammar! {
            char_prod_rule! { 'E' => <'b''F'> },
            char_prod_rule! { 'F' => <'a''F'>, <> }
        };

        let first_e = g.first(char_prod_rhs!(<'E'>).iter());

        assert_eq!(first_e.toks, HashSet::from(['b']));
        assert_eq!(first_e.nullable, false);

        let first_f = g.first(char_prod_rhs!(<'F'>).iter());

        assert_eq!(first_f.toks, HashSet::from(['a']));
        assert_eq!(first_f.nullable, true);
    }

    #[test]
    fn empty_follows()
    {
        let g = grammar! {
            char_prod_rule! { 'E' => <'b''F'> },
            char_prod_rule! { 'F' => <'a''F'>, <> }
        };

        let follow_map = g.follow_map();

        assert_eq!(follow_map.get(&'E'), Some(&HashSet::new()));
        assert_eq!(follow_map.get(&'F'), Some(&HashSet::new()));
    }

    #[test]
    fn simple_follows()
    {
        let g = grammar! {
            char_prod_rule! { 'E' => <'b''F''e'> },
            char_prod_rule! { 'F' => <'a''F'>, <> }
        };

        let follow_map = g.follow_map();

        assert_eq!(follow_map.get(&'E'), Some(&HashSet::new()));
        assert_eq!(follow_map.get(&'F'), Some(&HashSet::from(['e'])));
    }

    #[test]
    fn complex_follows()
    {
        let g = grammar! {
            char_prod_rule! { 'S' => <'u''B''D''z'> },
            char_prod_rule! { 'B' => <'w''C'> },
            char_prod_rule! { 'C' => <'v''C'>, <> },
            char_prod_rule! { 'D' => <'E''F'> },
            char_prod_rule! { 'E' => <'y'>, <> },
            char_prod_rule! { 'F' => <'x'>, <> }
        };

        let follow_map = g.follow_map();

        assert_eq!(follow_map.get(&'S'), Some(&HashSet::new()));
        assert_eq!(follow_map.get(&'B'), Some(&HashSet::from(['x', 'y', 'z'])));
        assert_eq!(follow_map.get(&'C'), Some(&HashSet::from(['x', 'y', 'z'])));
        assert_eq!(follow_map.get(&'D'), Some(&HashSet::from(['z'])));
        assert_eq!(follow_map.get(&'E'), Some(&HashSet::from(['x', 'z'])));
        assert_eq!(follow_map.get(&'F'), Some(&HashSet::from(['z'])));
    }

    #[test]
    fn simple_parser()
    {
        let g = grammar! {
            char_prod_rule! { 'E' => <'b''F''e'> },
            char_prod_rule! { 'F' => <'a''F'>, <> }
        };

        let parser = Parser::from(&g);

        assert_eq!(parser.entries.get(&'E'), Some(&ParserEntry {
            first: HashMap::from([(Some('b'), char_prod_rhs!(<'b''F''e'>))]),
            follow: HashSet::from([])
        }));

        assert_eq!(parser.entries.get(&'F'), Some(&ParserEntry {
            first: HashMap::from([(Some('a'), char_prod_rhs!(<'a''F'>)), (None, char_prod_rhs!(<>))]),
            follow: HashSet::from(['e'])
        }));
    }

    #[test]
    fn simple_parsing()
    {
        let g = grammar! {
            char_prod_rule! { 'E' => <'b''F''e'> },
            char_prod_rule! { 'F' => <'a''F'>, <> }       
        };

        let parser = Parser::from(&g);

        let res = parser.parse(&mut CharStream::from("baae"), 'E');

        assert_eq!(res, Some(ParseTree::Node {
            label: 'E',
            children: vec![
                ParseTree::Leaf('b'),
                ParseTree::Node { 
                    label: 'F', 
                    children: vec![
                        ParseTree::Leaf('a'),
                        ParseTree::Node {
                            label: 'F',
                            children: vec![
                                ParseTree::Leaf('a'),
                                ParseTree::Node { 
                                    label: 'F', 
                                    children: vec![]
                                }
                            ]
                        }
                    ]
                },
                ParseTree::Leaf('e')
            ]
        }))
    }

    #[test]
    fn expr_parsing() {
        #[derive(PartialEq, Eq, Debug)]
        enum Tokens {
            Ident(String),
            Number(u32),
            LParen,
            RParen,
            Plus,
            Times
        }

        impl Label<Tokens> for char
        {
            fn get_label(value: &Tokens) -> Self {
                match value {
                    Tokens::Ident(_) => 'i',
                    Tokens::Number(_) => 'n',
                    Tokens::LParen => '(',
                    Tokens::RParen => ')',
                    Tokens::Plus => '+',
                    Tokens::Times => '*'
                }
            }
        }

        let g = grammar! {
            char_prod_rule!( 'E' => <'T''U'>),
            char_prod_rule!( 'U' => <'+''T''U'>, <>),
            char_prod_rule!( 'T' => <'i''V'>, <'n''V'>, <'(''E'')''V'>),
            char_prod_rule!( 'V' => <'*''T'>, <>)
        };

        let parser = Parser::from(&g);

        let tokens = vec![
            Tokens::LParen,
            Tokens::Number(1),
            Tokens::Plus,
            Tokens::Ident("x".into()),
            Tokens::RParen,
            Tokens::Times,
            Tokens::Number(42)
        ];

        let res: Option<ParseTree<char, Tokens>> = parser.parse(&mut tokens.into_token_stream(), 'E');

        assert_eq!(res, Some(pt_node! { 'E';
            pt_node! { 'T';
                ParseTree::Leaf(Tokens::LParen),
                pt_node! { 'E' ;
                    pt_node! { 'T';
                        ParseTree::Leaf(Tokens::Number(1)),
                        pt_node! { 'V'; }
                    },
                    pt_node! { 'U';
                        ParseTree::Leaf(Tokens::Plus),
                        pt_node! { 'T';
                            ParseTree::Leaf(Tokens::Ident("x".into())),
                            pt_node! { 'V'; }
                        },
                        pt_node! { 'U'; }
                    }
                },
                ParseTree::Leaf(Tokens::RParen),
                pt_node! { 'V' ;
                    ParseTree::Leaf(Tokens::Times),
                    pt_node! { 'T';
                        ParseTree::Leaf(Tokens::Number(42)),
                        pt_node! { 'V'; }
                    }
                }
            },
            pt_node! { 'U'; }
        }));
    }
}

fn main() {
}
