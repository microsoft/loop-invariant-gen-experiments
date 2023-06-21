int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x2 = 0);
  assume((x1 >= 0));
  // loop body
  while ((x2 < x1)) {
    {
    (x2  = (x2 + 1));
    }

  }
  // post-condition
assert( (x2 == x1) );
}