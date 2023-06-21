int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  int x6;
  // pre-conditions
  (x3 = 0);
  (x1 = 1);
  // loop body
  while ((x1 <= x2)) {
    {
    (x1  = (x1 + 1));
    (x3  = (x3 + 1));
    }

  }
  // post-condition
if ( (x3 != 0) )
assert( (x3 == x2) );

}
