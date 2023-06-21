from pyparsing import *

# identifier = Word(alphas, alphanums + "_")
identifier = alphas | Word(alphas, alphanums + "_")
integer = Combine(Optional(oneOf("+ -")) + Word(nums))
operator = oneOf("+ - * / % > < >= <= == !=")
assignment_operator = oneOf("= += -= *= /=")
datatype = "int"
assume_keyword = "assume"
assert_keyword = "assert"
semicolon = Suppress(";")
lp = Suppress("(")
rp = Suppress(")")
lcp = Suppress("{")
rcp = Suppress("}")

comment = Suppress(Group("/*" + SkipTo("*/") + "*/") | Group("//" + SkipTo(LineEnd())))

variable_declaration = Group(datatype + identifier + "=" + integer) | Group(datatype + identifier)

expression = Forward()
expression <<  ("unknown()"
               | integer
               | identifier
               | Group((integer | identifier) + operator + expression)
               | lp + expression + rp
               )

assignment_expression = Forward()
assignment_expression << (Group(identifier + assignment_operator + expression)
               | lp + assignment_expression + rp
               )

assume_expression = Group(assume_keyword + "(" + expression + ")")
assert_expression = Group(assert_keyword + "(" + expression + ")")

# statements = Forward()
if_then_else = Forward()
while_loop = Forward()

# statement = ((assignment_expression | assume_expression | assert_expression | variable_declaration | if_then_else | while_loop) + semicolon)
# statements << (OneOrMore(statement)
#                | Group("{" + statements + "}")
#                )

# if_then_else << (Group("if" + "(" + expression + ")" + "{" + statements + "}")
#                  | Group("if" + "(" + expression + ")" + "{" + statements + "}" + "else" + "{" + statements + "}")
#                  | Group("if" + "(" + expression + ")" + "{" + statements + "}" + "else if" + "(" + expression + ")" + "{" + statements + "}" + "else" + "{" + statements + "}")
#                 )

# while_loop << Group("while" + "(" + expression + ")" + "{" + statements + "}")

statement = (assume_expression + semicolon 
             | assert_expression + semicolon 
             | variable_declaration + semicolon
             | assignment_expression + semicolon 
             | if_then_else
             | while_loop)
statements = OneOrMore(statement)

block = Forward()
block << (statements | Group(lcp + block + rcp))

if_then_else << (Group("if" + "(" + expression + ")" + block)
                 | Group("if" + "(" + expression + ")" + block + "else" + block)
                 | Group("if" + "(" + expression + ")" + block + "else if" + "(" + expression + ")" + block + "else" + block)
                )

while_loop << Group("while" + "(" + expression + ")" + block)

# statements << OneOrMore(statement | block)

# preconditions = ZeroOrMore(assignment_expression) + ZeroOrMore(assume_expression)

# postconditions = if_then_else | statements


program = Suppress(Group(datatype + identifier + "()")) + block

program.ignore(comment)

test = """
int main() {
  assume((n > 0));
}
"""
res = program.parseString(test)

# res = program.parseFile("57.c")

breakpoint()