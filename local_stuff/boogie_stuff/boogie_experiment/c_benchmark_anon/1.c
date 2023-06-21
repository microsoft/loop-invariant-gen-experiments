int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x1 = 1);
  (x2 = 0);
  // loop body
  while ((x2 < 100000)) {
    {
    (x1  = (x1 + x2));
    (x2  = (x2 + 1));
    }

  }
  // post-condition
assert( (x1 >= x2) );
}