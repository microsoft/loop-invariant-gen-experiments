int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x1 = -5000);
  // loop body
  while ((x1 < 0)) {
    {
    (x1  = (x1 + x2));
    (x2  = (x2 + 1));
    }

  }
  // post-condition
assert( (x2 > 0) );
}
