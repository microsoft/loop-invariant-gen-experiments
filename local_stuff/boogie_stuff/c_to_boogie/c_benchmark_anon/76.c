int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  int x6;
  // pre-conditions
  (x1 = 0);
  assume((x5 >= 0));
  assume((x5 >= 127));
  (x6 = (36 * x5));
  // loop body
  while (unknown()) {
    if ( (x1 < 36) )
    {
    (x6  = (x6 + 1));
    (x1  = (x1 + 1));
    }

  }
  // post-condition
if ( (x6 < 0) )
if ( (x6 >= 4608) )
assert( (x1 >= 36) );

}
