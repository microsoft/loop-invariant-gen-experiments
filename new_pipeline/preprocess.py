import os

from tree_sitter import Language, Parser

lib_path = os.path.join(os.path.dirname(__file__), "tree_sitter_lib/build/")
language = Language(lib_path + "c-tree-sitter.so", "c")
parser = Parser()
parser.set_language(language)


def remove_comments(code):
    comment_query = language.query(
        """
        (comment) @comment 
        """
    )
    ast = parser.parse(bytes(code, "utf-8"))
    comments = comment_query.captures(ast.root_node)
    comments = sorted(comments, key=lambda x: x[0].start_byte, reverse=True)
    for comment in comments:
        code = code[: comment[0].start_byte] + code[comment[0].end_byte :]
    return code


c = """/*
Commit Number: c3115350eb8bb635d0fdb4dbbb0d0541f38ed19c
URL: https://github.com/Sugon-Beijing/libvncserver/commit/c3115350eb8bb635d0fdb4dbbb0d0541f38ed19c
Project Name: libvncserver
License: GPL-2.0
termination: TRUE
*/
int main()
{

    int linesToRead = __VERIFIER_nondet_int();
    if( linesToRead < 0 )
        return 0;
    int h = __VERIFIER_nondet_int();
    while( linesToRead && h > 0 )
    {
        if( linesToRead > h )
            linesToRead = h;
        h -= linesToRead;
    }
    return 0;

}
"""

c = remove_comments(c)
print(c)
