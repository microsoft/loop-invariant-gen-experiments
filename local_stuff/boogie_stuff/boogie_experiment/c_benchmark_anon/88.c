int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  // pre-conditions
  (x3 = (x2 + 1));
  (x1 = 0);
  // loop body
  while ((x2 != x3)) {
    {
      if ( unknown() ) {
        {
        (x1  = 1);
        (x2  = x3);
        }
      } else {
        {
        (x1  = 0);
        (x2  = x3);
        (x3  = (x3 + 1));
        }
      }

    }

  }
  // post-condition
assert( (x1 == 1) );
}
