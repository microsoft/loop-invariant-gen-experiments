int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  // pre-conditions
  (x2 = 0);
  (x1 = 0);
  (x4 = 1);
  // loop body
  while ((x1 <= x3)) {
    {
    (x1  = (x1 + 1));
    (x2  = (x2 + x4));
    }

  }
  // post-condition
if ( (x4 == 1) )
assert( (x1 == x2) );

}
