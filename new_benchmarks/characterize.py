import argparse
import os
import re
import sys
from pathlib import Path

import numpy as np
import pandas as pd
import tiktoken
from tree_sitter import Language, Parser


class BenchmmarkParser:

    def __init__(self, language_name):
        lib_path = os.path.join(os.path.dirname(__file__), 'tree_sitter_lib/build/')

        if language_name == "c":
            self.language = Language(lib_path + 'c-tree-sitter.so', language_name)
        elif language_name == "cpp":
            self.language = Language(lib_path + 'cpp-tree-sitter.so', language_name)
        else:
            raise ValueError("Unknown language name")
        
        self.parser = Parser()
        self.parser.set_language(self.language)
        self.queries = {}
        self.set_queries()

    def set_queries(self):
        self.queries['functions'] = self.language.query("""(function_definition) @function""")
        self.queries['loops'] = self.language.query("""[(for_statement) @for_loop 
                                                     (while_statement) @while_loop]""")
        self.queries['arrays'] = self.language.query("""(array_declarator) @array""")
        self.queries['pointers'] = self.language.query("""(pointer_declarator) @pointer""")
        self.queries['structs'] = self.language.query("""(struct_specifier) @struct""")
        if self.language.name == "cpp":
            self.queries['classes'] = self.language.query("""(class_specifier) @class""")

    def token_length(self, code):
        encoding = tiktoken.encoding_for_model('gpt-4')
        num_tokens = len(encoding.encode(code))
        return num_tokens

    def calculate_stats(self, code):
        ast = self.parser.parse(bytes(code, "utf8"))
        multiline = ["functions", "loops"]
        memory = ["structs", "classes"]
        stats = {}
        for k, query in self.queries.items():
            stats[k + "_count"] =  0

            if k in multiline:
                stats[k + "_avg_tokens"] = 0
            if k in multiline + memory:
                stats[k + "_tokenized_sizes"] = []
            
            captures = query.captures(ast.root_node)

            for node in captures:
                stats[k + "_count"] += 1
                if k in multiline + memory:
                    stats[k + "_tokenized_sizes"].append(self.token_length(code[node[0].start_byte : node[0].end_byte]))
            
            if k in multiline and len(stats[k + "_tokenized_sizes"]) > 0:
                stats[k + "_avg_tokens"] = sum(stats[k + "_tokenized_sizes"]) / len(stats[k + "_tokenized_sizes"])

        modified_code = code
        block_comment_pattern = r'/\*.*?\*/'
        line_comment_pattern = r'//.*'

        modified_code = re.sub(block_comment_pattern, '', modified_code, flags=re.DOTALL)  
        modified_code = re.sub(line_comment_pattern, '', modified_code)
        code_length = self.token_length(modified_code)
        stats["num_code_tokens"] = code_length

        df = pd.DataFrame.from_dict(stats, orient='index').transpose()
        return df

    def parse(self, code):
        return self.parser.parse(bytes(code, "utf8"))
  

def parse_args(args):
    argparser = argparse.ArgumentParser(description="Characterize C code")
    argparser.add_argument("-i", "--input-directory", help="Input directory")
    argparser.add_argument("-o", "--output-file", help="Output file")
    args = argparser.parse_args(args)
    return args


def main(args):
    df = pd.DataFrame(columns=['benchmark', 'num_code_tokens', 'functions_count', 'functions_avg_tokens', 'functions_tokenized_sizes', 'loops_count', 'loops_avg_tokens', 'loops_tokenized_sizes', \
                                'arrays_count', 'pointers_count', 'structs_count', 'structs_tokenized_sizes', 'classes_count', 'classes_tokenized_sizes'])
    if args.input_directory:
        directories = []
        files = []
        if ',' in args.input_directory:
            directories = args.input_directory.split(',')
        else:
            directories = [args.input_directory]
        files = []
        for directory in directories:
            if not os.path.isdir(directory):
                print(f"Invalid input directory: {directory}")
                exit(1)
            files.extend([str(x) for x in list(Path(directory).rglob("*.[c|cpp]"))])

        for file in files:
            parser = None
            if file.endswith(".c"):
                parser = BenchmmarkParser('c')
            elif file.endswith(".cpp"):
                parser = BenchmmarkParser('cpp')
            else:
                continue

            with open(file, "r") as f:
                code = f.read()
                stats = parser.calculate_stats(code)
                stats['benchmark'] = file
                df = pd.concat([df, stats], ignore_index=True)
        df.set_index('benchmark', inplace=True)
    else:
        print("Invalid input directory")
        exit(1)
    if args.output_file:
        df.to_excel(args.output_file)
        print(f"Saved to {args.output_file}")
    else:
        print(df)


if __name__ == "__main__":
    main(parse_args(sys.argv[1:]))

