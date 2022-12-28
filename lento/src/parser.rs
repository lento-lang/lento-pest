use pest::{Parser, iterators::{Pairs}, pratt_parser::{PrattParser, Op, Assoc::*}};
use pest_ascii_tree::print_ascii_tree;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct LentoParser;

pub fn parse_program(source: &str) -> Result<Pairs<'_, Rule>, pest::error::Error<Rule>> {
    let program = LentoParser::parse(Rule::program, source);
    let pratt = PrattParser::new()
        .op(Op::infix(Rule::infix_op, Left));
    let pairs = pratt
        .map_primary(|primary| match primary.as_rule() {

        })
        .parse(program.unwrap().next().unwrap());
    return pairs;
}

pub fn print_pairs(pairs: Pairs<'_, Rule>) {
    print_ascii_tree(Ok(pairs));
}
