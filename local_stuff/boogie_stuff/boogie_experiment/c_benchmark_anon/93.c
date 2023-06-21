int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  // pre-conditions
  assume((x2 >= 0));
  (x1 = 0);
  (x3 = 0);
  (x4 = 0);
  // loop body
  while ((x1 < x2)) {
    {
    (x1  = (x1 + 1));
      if ( unknown() ) {
        {
        (x3  = (x3 + 1));
        (x4  = (x4 + 2));
        }
      } else {
        {
        (x3  = (x3 + 2));
        (x4  = (x4 + 1));
        }
      }

    }

  }
  // post-condition
assert( ((3 * x2) == (x3 + x4)) );
}
