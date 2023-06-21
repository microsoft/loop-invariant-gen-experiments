int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x1 = 1);
  (x2 = 10);
  // loop body
  while ((x2 >= x1)) {
    {
    (x1  = (x1 + 2));
    (x2  = (x2 - 1));
    }

  }
  // post-condition
assert( (x2 == 6) );
}
