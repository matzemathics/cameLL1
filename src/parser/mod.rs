use std::fmt::Debug;
use std::hash::Hash;
use std::collections::HashSet;
use std::collections::HashMap;
use std::iter::Peekable;
use std::marker::PhantomData;
use std::str::Chars;
use either::Either;

#[cfg(test)]
mod test;

use crate::grammar::{RuleStr, Grammar};

#[derive(Debug)]
pub struct ParserEntry<Nt, Tok> {
    pub(in crate) first: HashMap<Option<Tok>, RuleStr<Nt, Tok>>,
    pub(in crate) follow: HashSet<Tok>
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

pub struct Parser<Nt, Tok> {
    pub(in crate) entries: HashMap<Nt, ParserEntry<Nt, Tok>>
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
pub enum ParseTree<Nt, Tok> {
    Leaf(Tok),
    Node {
        label: Nt,
        children: Vec<ParseTree<Nt, Tok>>
    }
}

pub trait TokenStream: Iterator
where
    Self::Label: Label<Self::Item>
{
    type Label;

    fn peek_label(&mut self) -> Option<Self::Label>;
}

pub trait Label<T>: Eq+Hash+Copy {
    fn get_label(value: &T) -> Self;
}

impl<T: Copy+Eq+Hash> Label<T> for T {
    fn get_label(value: &T) -> Self {
        *value
    }
}

pub trait IntoTokenStream<L>
where
    L: Label<Self::Item>,
    Self::IntoTokenStream: TokenStream<Label = L, Item = Self::Item>,
{
    type Item;
    type IntoTokenStream;

    fn into_token_stream(self) -> Self::IntoTokenStream;
}

pub struct LabeldStream<T, L> {
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

pub struct CharStream<T: Iterator<Item = char>>(Peekable<T>);

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

    pub fn parse<T, I>(&self, stream: &mut T, start: Nt) -> Option<ParseTree<Nt, I>>
    where
        T: TokenStream<Label = Tok, Item = I>,
        Tok: Label<I>+Debug
    {
        let mut children = Vec::new();

        let curr_tok = stream.peek_label();
        let rule = self.select_rule(start, curr_tok)?;

        for it in rule.iter() {
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

