from tree_sitter import Language

"""
Clone the tree-sitter-c repository to tree_sitter_lib/vendor/
The output of this build is tree_sitter_lib/build/c-tree-sitter.so
"""
Language.build_library(
  'tree_sitter_lib/build/c-tree-sitter.so',
  [
    'tree_sitter_lib/vendor/tree-sitter-c'
  ]
)
