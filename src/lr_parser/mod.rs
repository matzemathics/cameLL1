use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

use either::Either;

use crate::grammar::{Grammar, RuleStr};
use crate::parser::ParseTree;

struct LrParser<St, Nt, Tok> {
    states: HashMap<(St, Option<Tok>), LrAction<St, Nt>>,
    gotos: HashMap<(St, Nt), St>,
    start: St,
}

enum LrAction<St, Nt> {
    Shift(St),
    Reduce(usize, Nt),
    Accept,
}

#[derive(PartialEq, Eq, Hash, Clone)]
struct LrzItem<Nt, Tok> {
    lhs: Nt,
    rhs: RuleStr<Nt, Tok>,
    pos: usize,
}

impl<Nt, Tok> LrzItem<Nt, Tok> {
    fn fst(&self) -> Option<&Either<Nt, Tok>> {
        if self.pos < self.rhs.len() {
            Some(&self.rhs[self.pos])
        } else {
            None
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
struct LrzState<Nt, Tok> {
    items: Vec<LrzItem<Nt, Tok>>,
}

impl<Nt, Tok> FromIterator<LrzItem<Nt, Tok>> for LrzState<Nt, Tok> {
    fn from_iter<T: IntoIterator<Item = LrzItem<Nt, Tok>>>(iter: T) -> Self {
        LrzState {
            items: iter.into_iter().collect(),
        }
    }
}

impl<Nt, Tok> LrzState<Nt, Tok>
where
    Nt: Eq + Copy + Hash,
    Tok: Eq + Copy,
{
    fn shift_goto(self, sym: Either<Nt, Tok>) -> LrzState<Nt, Tok> {
        self.items
            .into_iter()
            .filter_map(|mut x| {
                if x.fst() == Some(&sym) {
                    x.pos += 1;
                    Some(x)
                } else {
                    None
                }
            })
            .collect()
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    fn closure(&mut self, grammar: &Grammar<Nt, Tok>) {
        let mut nts = HashSet::new();

        let mut new_items = Vec::new();
        loop {
            for item in &self.items {
                if let Either::Left(nt) = item.rhs[item.pos] {
                    if nts.insert(nt) {
                        grammar.productions[&nt]
                            .iter()
                            .map(|r| LrzItem {
                                lhs: nt,
                                rhs: r.clone(),
                                pos: 0,
                            })
                            .collect_into(&mut new_items);
                    }
                }
            }

            if new_items.is_empty() {
                break;
            }

            self.items.append(&mut new_items);
        }
    }
}

impl<Nt, Tok> LrParser<usize, Nt, Tok>
where
    Nt: Eq + Hash + Copy,
    Tok: Eq + Hash + Copy,
{
    fn build(grammar: &Grammar<Nt, Tok>, start: Nt) -> LrParser<usize, Nt, Tok> {
        let start_rules = grammar.productions.get(&start).unwrap();
        let mut start_state: LrzState<_, _> = start_rules
            .iter()
            .map(|r| LrzItem {
                lhs: start,
                rhs: r.clone(),
                pos: 0,
            })
            .collect();

        start_state.closure(grammar);

        let mut unvisited = VecDeque::new();
        unvisited.push_back((start_state, None));

        let mut visited: HashMap<LrzState<_, _>, (u32, Vec<_>)> = HashMap::new();
        let mut counter = 0;

        while let Some((st, root)) = unvisited.pop_front() {
            let root_idx = root.map(|r| (*visited.get(&r).unwrap()).0);
            let ins_res = visited.try_insert(st.clone(), (counter, vec![]));

            if ins_res.is_ok() {
                counter += 1;
                let paths: Vec<_> = st.items.iter().filter_map(|it| it.fst()).collect();

                for it in paths {
                    let mut chld = st.clone().shift_goto(*it);
                    chld.closure(grammar);
                    unvisited.push_back((chld, Some(st.clone())));
                }
            }

            if let Some(root_idx) = root_idx {
                match ins_res {
                    Ok((_, origs)) => origs.push(root_idx),
                    Err(mut e) => e.entry.get_mut().1.push(root_idx),
                }
            }
        }

        todo!()
    }
}

impl<St, Nt, Tok> LrParser<St, Nt, Tok>
where
    St: Eq + Copy + Hash,
    Nt: Eq + Hash + Copy + Debug,
    Tok: Eq + Hash + Copy,
{
    fn parse(&self, mut input: impl Iterator<Item = Tok>) -> Option<ParseTree<Nt, Tok>> {
        let mut progress: Vec<ParseTree<Nt, Tok>> = Vec::new();
        let mut stack = vec![self.start];

        let mut curr = input.next();

        loop {
            let action = self.states.get(&(*stack.last().unwrap(), curr))?;

            match action {
                LrAction::Shift(st) => {
                    stack.push(*st);
                    progress.push(ParseTree::Leaf(curr.unwrap()));
                    curr = input.next();
                }
                LrAction::Reduce(num, nt) => {
                    let node = ParseTree::Node {
                        label: *nt,
                        children: progress.drain(progress.len() - num..).collect(),
                    };
                    progress.push(node);
                    stack.drain(stack.len() - num..);
                    stack.push(*self.gotos.get(&(*stack.last().unwrap(), *nt))?);
                }
                LrAction::Accept => {
                    assert_eq!(progress.len(), 1);
                    break progress.pop();
                }
            }
        }
    }
}

macro_rules! map {
    { $($($e:expr),+ => $t:expr),* } => {
        HashMap::from([ $((($($e),+), $t)),+ ])
    };
}

mod test {
    use std::collections::HashMap;

    use crate::parser::ParseTree;

    use super::{LrAction, LrParser};

    #[test]
    fn lr_parsing() {
        let parser = LrParser {
            states: map! {
                1, Some('x') => LrAction::Shift(5),
                2, None => LrAction::Accept,
                3, Some('x') => LrAction::Reduce(1, 'E'),
                3, Some('+') => LrAction::Shift(4),
                3, None => LrAction::Reduce(1, 'E'),
                4, Some('x') => LrAction::Shift(5),
                5, Some('x') => LrAction::Reduce(1, 'T'),
                5, Some('+') => LrAction::Reduce(1, 'T'),
                5, None => LrAction::Reduce(1, 'T'),
                6, Some('x') => LrAction::Reduce(3, 'E'),
                6, Some('+') => LrAction::Reduce(3, 'E'),
                6, None => LrAction::Reduce(3, 'E')
            },
            gotos: map! {
                1, 'E' => 2,
                1, 'T' => 3,
                4, 'E' => 6,
                4, 'T' => 3
            },
            start: 1,
        };

        let res = parser.parse("x+x+x".chars()).unwrap();

        assert_eq!(
            res,
            ParseTree::Node {
                label: 'E',
                children: vec![
                    ParseTree::Node {
                        label: 'T',
                        children: vec![ParseTree::Leaf('x')]
                    },
                    ParseTree::Leaf('+'),
                    ParseTree::Node {
                        label: 'E',
                        children: vec![
                            ParseTree::Node {
                                label: 'T',
                                children: vec![ParseTree::Leaf('x')]
                            },
                            ParseTree::Leaf('+'),
                            ParseTree::Node {
                                label: 'E',
                                children: vec![ParseTree::Node {
                                    label: 'T',
                                    children: vec![ParseTree::Leaf('x')]
                                }]
                            }
                        ]
                    }
                ]
            }
        )
    }
}
