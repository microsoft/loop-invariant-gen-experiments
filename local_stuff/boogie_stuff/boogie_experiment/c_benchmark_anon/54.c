int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  // pre-conditions
  (x1 = 0);
  assume((x2 > 0));
  // loop body
  while (unknown()) {
    {
      if ( unknown() ) {
        if ( (x1 > x2) )
        {
        (x1  = (x1 + 1));
        }
      } else {
        if ( (x1 == x2) )
        {
        (x1  = 1);
        }
      }

    }

  }
  // post-condition
if ( (x1 != x2) )
assert( (x1 <= x2) );
}