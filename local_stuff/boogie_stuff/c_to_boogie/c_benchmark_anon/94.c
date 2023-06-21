int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  // pre-conditions
  assume((x3 >= 0));
  assume((x4 >= 0));
  (x1 = 0);
  (x2 = 0);
  // loop body
  while ((x1 <= x4)) {
    {
    (x1  = (x1 + 1));
    (x2  = (x2 + x1));
    }

  }
  // post-condition
assert( ((x1 + (x2 + x3)) > (2 * x4)) );
}
