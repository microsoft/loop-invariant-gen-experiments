- accelerating_invariant_generation/crafted is not translated because our C-to-Boogie translator doesn't support integer overflow.
- accelerating_invariant_generation/svcomp - veri*.c files and vogal*.c files are not translated because our C-to-Boogie translator doesn't handle char.

Steps:
- Move files to be translated from original_benchmarks into translated_benchmarks after necessary modifications for parser (lark_parser.py)
- Run filter.py
- Run `python parse_checker.py parser`
- Run `python parse_checker.py boogie`