use std::collections::HashSet;
use either::Either;

macro_rules! char_prod_rhs {
    (<>) => { crate::grammar::RuleStr::from(vec![]) };
    (<$($sym:literal)+>) => {
        crate::grammar::RuleStr::from(vec![
            $(if $sym.is_uppercase() { either::Either::Left($sym) }
            else { either::Either::Right($sym) }),+
        ])
    };
}

macro_rules! char_prod_rule {
    ($lhs:expr => $(<$($rhs:literal)*>),+) => {
        crate::grammar::Production { lhs: $lhs, rhs: vec![ $( char_prod_rhs!(<$($rhs)*>) ),+ ] }
    };
}

macro_rules! grammar {
    ($($($rule:tt)+);*) => {
        [ $( $($rule)+ )* ].into_iter().collect::<crate::grammar::Grammar<_,_>>()
    }
}

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