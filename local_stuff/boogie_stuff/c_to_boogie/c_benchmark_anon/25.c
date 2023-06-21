int main() {
  // variable declarations
  int x1;
  // pre-conditions
  (x1 = 10000);
  // loop body
  while ((x1 > 0)) {
    {
    (x1  = (x1 - 1));
    }

  }
  // post-condition
assert( (x1 == 0) );
}
