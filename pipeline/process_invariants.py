import sys
import os
from lark import Lark, Transformer

predicate_grammar = r"""
    term: VAR | NUMBER | term bin_op term | LPAREN term RPAREN

    bin_op : "+" | "-" | "*" | "/" | "%" | "^^" | "<<" | ">>" | "&" | "|" | "-->" | "<-->" | "^"

    ?pred: TRUE | FALSE
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

    rel_op : EQUALS | NOTEQUALS | LESSTHAN | GREATERTHAN | LESSTHANEQUALS | GREATERTHANEQUALS

    EQUALS: "=="
    NOTEQUALS: "!="
    LESSTHAN: "<"
    GREATERTHAN: ">"
    LESSTHANEQUALS: "<="
    GREATERTHANEQUALS: ">="

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
ast = parser.parse("x == 1 && y == 2")
print(ast)

class PredicateTransformer(Transformer):
    def __init__(self):
        self.predicates = []
        self.terms = []

    def pred(self, args):
        print(args)
        self.predicates.append(args)

    def term(self, args):
        self.terms.append(args)
        print(args)
        return ''.join(args)

    def VAR(self, args):
        return args[0]
    
    def NUMBER(self, args):
        return args[0]
    
    def TRUE(self, args):
        return "True"
    
    def FALSE(self, args):
        return "False"
    
    def LPAREN(self, args):
        return "("
    
    def RPAREN(self, args):
        return ")"
    
    def LAND(self, args):
        return "and"
    
    def LOR(self, args):
        return "or"
    
    def LIMPL(self, args):
        return "implies"
    
    def LBIIMPL(self, args):
        return "iff"
    
    def LNOT(self, args):
        return "not"
    
    def LXOR(self, args):
        return "xor"
    
    def TERNOP(self, args):
        return "if"
    
    def COLON(self, args):
        return "else"
    
    def SEMICOLON(self, args):
        return ";"
    
    def FORALL(self, args):
        return "forall"
    
    def EXISTS(self, args):
        return "exists"
    
    def bin_op(self, args):
        return args[0]
    
    def rel_op(self, args):
        return args[0]

transformer = PredicateTransformer()
transformer.transform(ast)
print(transformer.predicates)
