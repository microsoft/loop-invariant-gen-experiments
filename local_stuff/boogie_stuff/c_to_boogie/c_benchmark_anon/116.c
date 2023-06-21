int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  // pre-conditions
  (x1 = 0);
  (x5 = 0);
  // loop body
  while (unknown()) {
    {
    (x5  = (x5 + 1));
    (x1  = (x1 + 1));
    }

  }
  // post-condition
if ( (x1 != x5) )
assert( (x1 == -1) );

}
