use std::collections::{HashMap, HashSet};

use crate::parser::{Parser, ParserEntry, ParseTree, CharStream, IntoTokenStream, Label};

macro_rules! pt_node {
    ( $label:expr ; $($child:expr),* ) => {
        crate::parser::ParseTree::Node {
            label: $label,
            children: vec! [ $($child),* ]
        }
    };
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