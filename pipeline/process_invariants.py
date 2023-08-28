import sys
import os
from lark import Lark, Transformer

predicate_grammar = r"""
    term: VAR | NUMBER | unary_op term | term bin_op term | LPAREN term RPAREN | term TERNOP term COLON term

    !unary_op : "+" | "-" | "!" 

    !bin_op : "+" | "-" | "*" | "/" | "%" | "^^" | "<<" | ">>" | "&" | "|" | "-->" | "<-->" | "^" | rel_op

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

    !rel_op : "==" | "!=" | "<" | ">" | "<=" | ">="

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

parser = Lark(predicate_grammar, parser='lalr', start='pred')
ast = parser.parse("j == (flag ? ((y * (y + 1)) / 2) + !y : (MAX * (y + 1)) / 2)")

class PredicateTransformer(Transformer):
    def __init__(self):
        self.predicates = []
        self.terms = []
        self.variables = {}
        self.literals

    def pred(self, args):
        string = ' '.join(args)
        self.predicates.append(string)
        return string

    def term(self, args):
        string = ' '.join(args)
        self.terms.append(string)
        return string

    def VAR(self, args):
        string = str(args)
        self.variables[string] = True
        return string
    
    def NUMBER(self, args):
        return args[0]

    def bin_op(self, args):
        return args[0]
    
    def unary_op(self, args):
        return args[0]
    
    def rel_op(self, args):
        return args[0]
    
    def __default_token__(self, token):
        return str(token)

transformer = PredicateTransformer()
transformer.transform(ast)
# print(transformer.predicates)
print(transformer.terms)
print(len(transformer.terms))
print(transformer.variables.keys())
