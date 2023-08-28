import sys
import os
from lark import Lark, Transformer

predicate_grammar = r"""
    pred: TRUE | FALSE
        | LPAREN pred RPAREN
        | term (rel_op term)+
        | pred LAND pred
        | pred LOR pred
        | pred LIMPL pred
        | pred LBIIMPL pred
        | LNOT pred
        | pred LXOR pred
        | term TERNOP pred COLON pred
        | pred TERNOP pred COLON pred

    term: VAR | NUMBER | term OP term

    rel_op : "==" | "!=" | "<=" | ">=" | ">" | "<"

    OP: "+" | "-" | "*" | "/" | "%" | "^" | ">>" | "<<" | "&" | "|" | "!" | "&&" | "||" | "^^"
    VAR: /[a-zA-Z_][a-zA-Z0-9_]*/
    NUMBER: /[0-9]+/

    TRUE : "\\true"
    FALSE: "\\false"
    LPAREN: "("
    RPAREN: ")"
    LAND: "&&"
    LOR: "\|\|"
    LIMPL: "==>"
    LBIIMPL: "<==>"
    LNOT: "!"
    LXOR: "^^"
    TERNOP: "?"
    COLON: ":"
    SEMICOLON: ";"
    FORALL: "\\forall"
    EXISTS: "\\exists"

    %import common.WS
    %ignore WS
"""

parser = Lark(predicate_grammar, parser='lalr', start="pred")
ast = parser.parse("x && y")