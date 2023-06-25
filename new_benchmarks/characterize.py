from tree_sitter import Language, Parser
import sys, os

Language.build_library(
  # Store the library in the `build` directory
  'tree-sitter-stuff/build/my-languages.so',

  # Include one or more languages
  [
    'tree-sitter-stuff/vendor/tree-sitter-c'
  ]
)

C_LANGUAGE = Language('tree-sitter-stuff/build/my-languages.so', 'c')

parser = Parser()
parser.set_language(C_LANGUAGE)

# tree = parser.parse(bytes("""
# int main() {
#     while(1){}
#     for(;;){}
#     int a[];
#     int *a = {1, 2, 3, 4};
#     return 0;
# }

# int foo();
# """, "utf8"))
# print(tree.root_node.sexp())
# print(tree.root_node.sexp().count("function_declarator"))
# print(tree.root_node.sexp().count("for_statement"))
# print(tree.root_node.sexp().count("while_statement"))
# print(tree.root_node.sexp().count("array"))
# print(tree.root_node.sexp().count("pointer"))

def output_stats_to_markdown(stats):
    s = ""
    s += "| Attribute | Number of Files |\n"
    s += "| --------- | --------------- |\n"
    for key, val in stats.items():
        s += f"| {key} | {val} |\n"
    return s

def characterize(code):
    tree = parser.parse(bytes(code, "utf8"))
    # return dictionary of counts
    results = {
        "function": tree.root_node.sexp().count("function_definition"),
        "for_loop": tree.root_node.sexp().count("for_statement"),
        "while_loop": tree.root_node.sexp().count("while_statement"),
        "array": tree.root_node.sexp().count("array"),
        "pointer": tree.root_node.sexp().count("pointer")
    }

    return results

if len(sys.argv) != 2:
    print("Usage: python characterize.py [<file>|<dir_path>]")
    exit(1)

stats = None
if sys.argv[1].endswith(".c"):
    stats = characterize(open(sys.argv[1], "r").read())
elif os.path.exists(sys.argv[1]):
# MD: attribute, num of files containing attribute
    stats = {
        "total files": 0,
        "contains 1 function": 0,
        "contains >1 function": 0,
        "contains >1 loop": 0,
        "contains <=1 loop": 0,
        "contains array": 0,
        "contains pointer": 0
    }
    for root, dirs, files in os.walk(sys.argv[1]):
        for file in files:
            if not file.endswith(".c"): continue
            stats["total files"] += 1
            results = characterize(open(os.path.join(root, file), "r").read())
            if results["function"] == 1:
                stats["contains 1 function"] += 1
            if results["function"] > 1:
                stats["contains >1 function"] += 1
            if (results["for_loop"] + results["while_loop"]) > 1:
                stats["contains >1 loop"] += 1
            if (results["for_loop"] + results["while_loop"]) <= 1:
                stats["contains <=1 loop"] += 1
            if results["array"] > 0:
                stats["contains array"] += 1
            if results["pointer"] > 0:
                stats["contains pointer"] += 1
else:
    print("Invalid file or directory path")
    exit(1)

write_to_file = False
if write_to_file:
    input_path = sys.argv[2][:-1] if sys.argv[2].endswith("/") else sys.argv[2]
    dir_name = os.path.basename(input_path)
    dir_root = os.path.dirname(input_path)
    with open(os.path.join(dir_root, f"{dir_name}_stats.md"), "w") as f:
        f.write(output_stats_to_markdown(stats))
else:
    print(output_stats_to_markdown(stats))