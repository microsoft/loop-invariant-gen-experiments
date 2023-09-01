from lark import Lark

c_parser = Lark(r"""
    program: "int" "main" "(" ")" block
    
    block: statement
            | "{" statements "}"
    
    statements: statement+
    
    ?statement: assignment_expression ";"
            | assume_expression ";"
            | assert_expression ";"
            | variable_declaration ";"
            | unary_expression ";"
            | return_stmt ";"
            | break_stmt ";"
            | if_then_else
            | while_loop

    !return_stmt: "return"
    !break_stmt: "break"

    while_loop : "while" "(" expression ")" block

    if_then_else : "if" "(" expression ")" block
                | "if" "(" expression ")" block "else" block
                | "if" "(" expression ")" block "else if" "(" expression ")" block "else" block

    ?variable_list: identifier
                | identifier "," variable_list

    variable_declaration: data_type identifier "=" expression
                        | data_type variable_list
    
    !data_type: "int" | "bool"

    assert_expression: "assert" "(" expression ")"
    assume_expression: "assume" "(" expression ")"

    ?assignment_expression: identifier assignment_operator expression
                        | "(" assignment_expression ")"

    unknown: "unknown" "(" ")"
    unknown_int: "unknown_int" "(" ")"
    
    ?expression: unknown
                | unknown_int
                | integer
                | identifier
                | expression operator expression
                | unary_expression_operator expression
                | lbracket expression rbracket

    !lbracket: "("
    !rbracket: ")"

    ?unary_expression: identifier unary_operator
                    | unary_operator identifier
                    | "(" unary_expression ")"

    !assignment_operator: "="
                        | "+="
                        | "-="
                        | "*="
                        | "/="
                        | "%="

    !unary_operator: "++"
                    | "--"

    !unary_expression_operator: "!"
                            | "-"
                            | "+"
    
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
            | "||"
            | "&&"

    integer: SIGNED_NUMBER
    identifier: /[a-zA-Z_][a-zA-Z0-9_]*/ | /[a-zA-Z]/

    %import common.ESCAPED_STRING
    %import common.SIGNED_NUMBER
    %import common.WS
    %ignore WS

    COMMENT: "//" /[^\n]*/ _NEWLINE
            | "/*" /(.|\n|\r)+?/ "*/" _NEWLINE
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
        elif tree.data.value == "unknown_int": return self.visit_unknown_int(tree)
        elif tree.data.value == "while_loop": return self.visit_while_loop(tree)
        elif tree.data.value == "if_then_else": return self.visit_if_then_else(tree)
        elif tree.data.value == "unary_expression": return self.visit_unary_expression(tree)
        elif tree.data.value == "unary_expression_operator": return self.visit_unary_expression_operator(tree)
        elif tree.data.value == "block": return self.visit_block(tree)
        elif tree.data.value == "data_type": return self.visit_data_type(tree)
        elif tree.data.value == "return_stmt": return "return;"
        elif tree.data.value == "break_stmt": return "break;"
        elif tree.data.value == "lbracket": return "("
        elif tree.data.value == "rbracket": return ")"

    def visit_program(self, tree):
        return "procedure main() {\nvar nondet: bool;\nvar nondet_int: int;\n" + self.visit(tree.children[0]) + "}"
    
    def visit_statements(self, tree):
        output = ""
        delayed_output = ""
        for child in tree.children:
            semicolon = ''
            if child.data.value == "assignment_expression" or child.data.value == "assume_expression" or child.data.value == "assert_expression" or child.data.value == "variable_declaration" or child.data.value == "unary_expression":
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
    
    def visit_block(self, tree):
        return self.visit_statements(tree)
    
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
        if len(tree.children) == 2 and tree.children[1].data.value == "identifier":
            return "var " + self.visit(tree.children[1]) + ": " + self.visit(tree.children[0]), delayed_output
        elif len(tree.children) == 3 and tree.children[1].data.value == "identifier":
            delayed_output = self.visit(tree.children[1]) + " := " + self.visit(tree.children[2])
            return "var " + self.visit(tree.children[1]) + ": " + self.visit(tree.children[0]), delayed_output
        elif tree.children[1].data.value == "variable_list":
            out = ""
            var_list = self.visit(tree.children[1])
            data_type = self.visit(tree.children[0])
            for x in var_list[:-1]:
                out = out + "var " + x + ": " + f'{data_type};\n'
            out = out + "var " + var_list[-1] + ": " + data_type
            return out, delayed_output
        else:
            raise Exception("Error in variable declaration")
    
    def visit_data_type(self, tree):
        return tree.children[0].value
    
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
        elif len(tree.children) == 2:
            # this has to be unary_expression_operator
            return self.visit(tree.children[0]) + self.visit(tree.children[1])
        else:
            return self.visit(tree.children[0]) + self.visit(tree.children[1]) + self.visit(tree.children[2])
    
    def visit_unary_expression_operator(self, tree):
        return tree.children[0].value
        
    def visit_operator(self, tree):
        return " " + tree.children[0].value + " "
    
    def visit_assignment_operator(self, tree):
        return " " + tree.children[0].value + " "
    
    def visit_unknown(self, tree):
        return "nondet"
    
    def visit_unknown_int(self, tree):
        return "nondet_int"
    
    def visit_while_loop(self, tree):
        cond = self.visit(tree.children[0])
        body = self.visit(tree.children[1])
        if cond == "nondet":
            return "while(" + cond + ")\n// insert invariants \n{\n" + body + "//This comment is for codegen to add havoc nondet\n}"
        else:
            return "while(" + cond + ")\n// insert invariants \n{\n" + body + "}"
    
    def visit_if_then_else(self, tree):
        if len(tree.children) == 2:
            return "if(" + self.visit(tree.children[0]) + ") {\n" + self.visit(tree.children[1]) + "}"
        elif len(tree.children) == 3:
            return "if(" + self.visit(tree.children[0]) + ") {\n" + self.visit(tree.children[1]) + "} else {\n" + self.visit(tree.children[2]) + "}"
        elif len(tree.children) == 5:
            return "if(" + self.visit(tree.children[0]) + ") {\n" + self.visit(tree.children[1]) + "} else if(" + self.visit(tree.children[2]) + ") {\n" + self.visit(tree.children[3]) + "} else {\n" + self.visit(tree.children[4]) + "}"
        
    def visit_unary_expression(self, tree):
        id = None
        op = None
        if tree.children[0].data.value == "unary_operator":
            id = self.visit(tree.children[1])
            op = tree.children[0].children[0].value
        elif tree.children[1].data.value == "unary_operator":
            id = self.visit(tree.children[0])
            op = tree.children[1].children[0].value
        if id is not None and op is not None:
            if op == "++":
                return id + " := " + id + " + 1"
            else:
                return id + " := " + id + " - 1"

def transform1(lines):
    # boogie needs all variable declarations in the beginning of the main function. It can't be in the middle.
    output_lines = []
    declaration_lines = []
    for line in lines:
        if "var " not in line:
            output_lines.append(line)
        else:
            declaration_lines.append(line)
    # breakpoint()
    output_lines = output_lines[:1] + declaration_lines + output_lines[1:]
    return output_lines

def transform2(lines):
    #insert havoc nondet before every occurrence of nondet and likewise for nondet_int
    output_lines = []
    for line in lines:
        if "var nondet" not in line and "nondet" in line and "nondet_int" not in line:
            output_lines.append("havoc nondet;")
        if "var nondet_int" not in line and "nondet_int" in line:
            output_lines.append("havoc nondet_int;")
        output_lines.append(line)
    return output_lines

def parse_and_convert(text):
    res = c_parser.parse(text)
    boogie_text = Visit().visit(res)
    lines = boogie_text.splitlines()
    output_lines1 = transform1(lines)
    output_lines2 = transform2(output_lines1)
    final_output = '\n'.join(output_lines2)
    return final_output

import sys, os

if len(sys.argv) != 2: 
    print("Usage: python3 parser.py <file_to_parse>")
    exit(1)
text = open(sys.argv[1]).read()
# print(c_parser.parse(text).pretty())
print(parse_and_convert(text))

# for file in os.listdir("c_benchmark"):
#     if file.endswith(".c"):
#         with open(f"boogie_translated/{file[:-2]}.bpl", "w") as f:
#             input = open(os.path.join("c_benchmark", file)).read()
#             try:
#                 output = parse_and_convert(input)
#             except:
#                 print(f"Error in {file}")
#                 continue
#             f.write(output)