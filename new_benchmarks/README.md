- accelerating_invariant_generation/crafted is not translated because our C-to-Boogie translator doesn't support integer overflow.
- accelerating_invariant_generation/svcomp - veri*.c files and vogal*.c files are not translated because our C-to-Boogie translator doesn't handle char.

Steps:
- Move files to be translated from original_benchmarks into translated_benchmarks after necessary modifications for parser (lark_parser.py)
- Run filter.py
- Run `python parse_checker.py parser`
- Run `python parse_checker.py boogie`

Dependencies:
- tree-sitter (Python Bindings)

Tree-Sitter Instructions:
- Install tree-sitter: `pip3 install tree_sitter`
- Create a directory 'tree-sitter-stuff' with subdirectories 'build' and 'vendor'
- Clone tree-sitter-c in the vendor directory: `git clone https://github.com/tree-sitter/tree-sitter-c`
- Use characterize.py
