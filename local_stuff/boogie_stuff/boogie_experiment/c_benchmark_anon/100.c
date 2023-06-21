int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  // pre-conditions
  assume((x1 >= 0));
  (x2 = x1);
  (x3 = 0);
  // loop body
  while ((x2 > 0)) {
    {
    (x3  = (x3 + 1));
    (x2  = (x2 - 1));
    }

  }
  // post-condition
assert( (x3 == x1) );
}
