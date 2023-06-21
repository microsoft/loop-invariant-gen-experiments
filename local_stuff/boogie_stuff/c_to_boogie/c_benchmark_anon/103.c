int main() {
  // variable declarations
  int x1;
  // pre-conditions
  (x1 = 0);
  // loop body
  while ((x1 < 100)) {
    {
    (x1  = (x1 + 1));
    }

  }
  // post-condition
assert( (x1 == 100) );
}
