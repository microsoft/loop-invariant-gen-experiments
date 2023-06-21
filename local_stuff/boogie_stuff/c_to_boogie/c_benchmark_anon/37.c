int main() {
  // variable declarations
  int x1;
  // pre-conditions
  (x1 = 0);
  // loop body
  while (unknown()) {
    {
      if ( unknown() ) {
        if ( (x1 != 40) )
        {
        (x1  = (x1 + 1));
        }
      } else {
        if ( (x1 == 40) )
        {
        (x1  = 1);
        }
      }

    }

  }
  // post-condition
if ( (x1 < 0) )
if ( (x1 > 40) )
assert( (x1 == 40) );

}