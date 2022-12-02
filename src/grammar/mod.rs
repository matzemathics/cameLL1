use std::collections::{VecDeque, HashMap, HashSet};
use std::hash::Hash;
use std::fmt::Debug;
use std::ops::Deref;
use either::Either;
use multimap::MultiMap;

#[cfg(test)]
#[macro_use]
mod test;

pub struct First<Tok> {
    pub nullable: bool,
    pub toks: HashSet<Tok>,
}

pub struct Production<Nt, Tok> {
    pub lhs: Nt,
    pub rhs: Vec<RuleStr<Nt, Tok>>
}

#[derive(Debug)]
pub struct Grammar<Nt, Tok> {
    pub productions: HashMap<Nt, Vec<RuleStr<Nt, Tok>>>
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

pub trait Inexhaustible {
    fn new_unused<'a>(used: impl Iterator<Item = &'a Self>) -> Self
    where Self: 'a;
}

impl Inexhaustible for char {
    fn new_unused<'a>(used: impl Iterator<Item = &'a Self>) -> Self
    where Self: 'a {
        let m = *used.max().unwrap_or(&'A');

        char::try_from(Into::<u32>::into(m) + 1).expect("failed to create fresh symbol")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RuleStr<Nt, Tok> (Vec<Either<Nt, Tok>>);

impl<Nt, Tok, T> From<T> for RuleStr<Nt, Tok>
where T: Into<Vec<Either<Nt, Tok>>>
{
    fn from(value: T) -> Self {
        RuleStr(value.into())
    }
}

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

    pub fn transform_left_rec_scc(&mut self, start: Nt, unvisited: &mut HashSet<Nt>)
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
    pub fn first<'a>(&'a self, mut alpha: impl Iterator<Item = &'a Either<Nt, Tok>>) -> First<Tok>
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

    pub fn follow_map(&self) -> HashMap<Nt, HashSet<Tok>>
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

