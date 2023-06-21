from lark import Lark, Visitor

c_parser = Lark(r"""
    program: "int" "main" "(" ")" block
    
    ?block: statements
            | "{" block "}"
    
    statements: statement+
    
    ?statement: assignment_expression ";"
            | assume_expression ";"
            | assert_expression ";"
            | variable_declaration ";"
            | if_then_else
            | while_loop

    while_loop : "while" "(" expression ")" block

    if_then_else : "if" "(" expression ")" block
                | "if" "(" expression ")" block "else" block
                | "if" "(" expression ")" block "else if" "(" expression ")" block "else" block

    ?variable_list: identifier
                | identifier "," variable_list

    variable_declaration: "int" identifier "=" expression
                        | "int" variable_list

    assert_expression: "assert" "(" expression ")"
    assume_expression: "assume" "(" expression ")"

    ?assignment_expression: identifier assignment_operator expression
                        | "(" assignment_expression ")"

    unknown: "unknown" "(" ")"
    
    ?expression: unknown
                | integer
                | identifier
                | expression operator expression
                | "(" expression ")"

    !assignment_operator: "="
                        | "+="
                        | "-="
                        | "*="
                        | "/="
                        | "%="
    
    !operator: "+"
            | "-"
            | "*"
            | "/"
            | "%"
            | "=="
            | "!="
            | "<"
            | ">"
            | "<="
            | ">="

    integer: SIGNED_NUMBER
    identifier: /[a-zA-Z_][a-zA-Z0-9_]*/ | /[a-zA-Z]/

    %import common.ESCAPED_STRING
    %import common.SIGNED_NUMBER
    %import common.WS
    %ignore WS

    COMMENT: "//" /[^\n]*/ _NEWLINE
    _NEWLINE: "\n"
    %ignore COMMENT
    %ignore " "
""", start = 'program', parser="lalr")

class Visit:
    def __init__(self):
        pass

    def visit(self, tree):
        if tree.data.value == "program": return self.visit_program(tree)
        elif tree.data.value == "statements": return self.visit_statements(tree)
        elif tree.data.value == "variable_list": return self.visit_variable_list(tree)
        elif tree.data.value == "variable_declaration": return self.visit_variable_declaration(tree)
        elif tree.data.value == "identifier": return self.visit_identifier(tree)
        elif tree.data.value == "integer": return self.visit_integer(tree)
        elif tree.data.value == "assignment_expression": return self.visit_assignment_expression(tree)
        elif tree.data.value == "assume_expression": return self.visit_assume_expression(tree)
        elif tree.data.value == "assert_expression": return self.visit_assert_expression(tree)
        elif tree.data.value == "expression": return self.visit_expression(tree)
        elif tree.data.value == "operator": return self.visit_operator(tree)
        elif tree.data.value == "assignment_operator": return self.visit_assignment_operator(tree)
        elif tree.data.value == "unknown": return self.visit_unknown(tree)
        elif tree.data.value == "while_loop": return self.visit_while_loop(tree)
        elif tree.data.value == "if_then_else": return self.visit_if_then_else(tree)

    def visit_program(self, tree):
        return "procedure main() {\nvar nondet: int;\n" + self.visit(tree.children[0]) + "}"
    
    def visit_statements(self, tree):
        output = ""
        delayed_output = ""
        for child in tree.children:
            semicolon = ''
            if child.data.value == "assignment_expression" or child.data.value == "assume_expression" or child.data.value == "assert_expression" or child.data.value == "variable_declaration":
                semicolon = ';'
            if child.data.value == "variable_declaration":
                declaration, initialization = self.visit(child)
                output += declaration + semicolon + '\n'
                if initialization != "":
                    delayed_output += initialization + semicolon + '\n'
            else:
                output += delayed_output # to append all the delayed output for all variable declarations before the current statement
                delayed_output = ""
                output += self.visit(child) + semicolon + '\n'
        return output + delayed_output
    
    def visit_variable_list(self, tree):
        l = []
        for x in tree.children:
            if x.data.value == "identifier":
                l.append(self.visit(x))
            elif x.data.value == "variable_list":
                l += self.visit(x)
        return l
    
    def visit_variable_declaration(self, tree):
        delayed_output = ""
        if len(tree.children) == 1 and tree.children[0].data.value == "identifier":
            return "var " + self.visit(tree.children[0]) + ": " + 'int', delayed_output
        elif len(tree.children) == 2 and tree.children[0].data.value == "identifier":
            delayed_output = self.visit(tree.children[0]) + " := " + self.visit(tree.children[1])
            return "var " + self.visit(tree.children[0]) + ": " + 'int', delayed_output
        elif tree.children[0].data.value == "variable_list":
            out = ""
            var_list = self.visit(tree.children[0])
            for x in var_list[:-1]:
                out = out + "var " + x + ": " + 'int;\n'
            out = out + "var " + var_list[-1] + ": " + 'int'
            return out, delayed_output
        else:
            raise Exception("Error in variable declaration")
    
    def visit_identifier(self, tree):
        return tree.children[0].value
    
    def visit_integer(self, tree):
        return tree.children[0].value
    
    def visit_assignment_expression(self, tree):
        out = ""
        if self.visit(tree.children[1]) == " = ":
            out = self.visit(tree.children[0]) + " := " + self.visit(tree.children[2])
        elif self.visit(tree.children[1]) == " += ":
            out = self.visit(tree.children[0]) + " := " + self.visit(tree.children[0]) + " + " + self.visit(tree.children[2])
        elif self.visit(tree.children[1]) == " -= ":
            out = self.visit(tree.children[0]) + " := " + self.visit(tree.children[0]) + " - " + self.visit(tree.children[2])
        elif self.visit(tree.children[1]) == " *= ":
            out = self.visit(tree.children[0]) + " := " + self.visit(tree.children[0]) + " * " + self.visit(tree.children[2])
        elif self.visit(tree.children[1]) == " /= ":
            out = self.visit(tree.children[0]) + " := " + self.visit(tree.children[0]) + " / " + self.visit(tree.children[2])
        elif self.visit(tree.children[1]) == " %= ":
            out = self.visit(tree.children[0]) + " := " + self.visit(tree.children[0]) + " % " + self.visit(tree.children[2])
        return out
    
    def visit_assume_expression(self, tree):
        return "assume(" + self.visit(tree.children[0]) + ")"
    
    def visit_assert_expression(self, tree):
        return "assert(" + self.visit(tree.children[0]) + ")"
    
    def visit_expression(self, tree):
        if len(tree.children) == 1:
            return self.visit(tree.children[0])
        else:
            return self.visit(tree.children[0]) + self.visit(tree.children[1]) + self.visit(tree.children[2])
        
    def visit_operator(self, tree):
        return " " + tree.children[0].value + " "
    
    def visit_assignment_operator(self, tree):
        return " " + tree.children[0].value + " "
    
    def visit_unknown(self, tree):
        return "nondet"
    
    def visit_while_loop(self, tree):
        return "while(" + self.visit(tree.children[0]) + ")\n// insert invariants \n{\n" + self.visit(tree.children[1]) + "}"
    
    def visit_if_then_else(self, tree):
        if len(tree.children) == 2:
            return "if(" + self.visit(tree.children[0]) + ") {\n" + self.visit(tree.children[1]) + "}"
        elif len(tree.children) == 3:
            return "if(" + self.visit(tree.children[0]) + ") {\n" + self.visit(tree.children[1]) + "} else {\n" + self.visit(tree.children[2]) + "}"
        elif len(tree.children) == 5:
            return "if(" + self.visit(tree.children[0]) + ") {\n" + self.visit(tree.children[1]) + "} else if(" + self.visit(tree.children[2]) + ") {\n" + self.visit(tree.children[3]) + "} else {\n" + self.visit(tree.children[4]) + "}"
    

# breakpoint()
# postprocessing - insert havoc nondet before every occurrence of nondet

def parse_and_convert(text):
    res = c_parser.parse(text)
    boogie_text = Visit().visit(res)
    lines = boogie_text.splitlines()
    postprocessed_lines = []
    for line in lines:
        if "var nondet" not in line and "nondet" in line:
            postprocessed_lines.append("havoc nondet;")
        postprocessed_lines.append(line)
    final_output = '\n'.join(postprocessed_lines)
    return final_output

import sys, os

# if len(sys.argv) != 2: 
#     print("Usage: python3 parser.py <file_to_parse>")
#     exit(1)
# text = open(sys.argv[1]).read()
# print(c_parser.parse(text).pretty())
# print(parse_and_convert(text))

for file in os.listdir("c_benchmark"):
    if file.endswith(".c"):
        with open(f"boogie_translated/{file[:-2]}.bpl", "w") as f:
            input = open(os.path.join("c_benchmark", file)).read()
            try:
                output = parse_and_convert(input)
            except:
                print(f"Error in {file}")
                continue
            f.write(output)