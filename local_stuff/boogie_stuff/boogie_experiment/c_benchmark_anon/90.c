int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  int x6;
  // pre-conditions
  (x6 = (x5 + 1));
  (x1 = 0);
  // loop body
  while ((x5 != x6)) {
    {
      if ( unknown() ) {
        {
        (x1  = 1);
        (x5  = x6);
        }
      } else {
        {
        (x1  = 0);
        (x5  = x6);
        (x6  = (x6 + 1));
        }
      }

    }

  }
  // post-condition
assert( (x1 == 1) );
}
