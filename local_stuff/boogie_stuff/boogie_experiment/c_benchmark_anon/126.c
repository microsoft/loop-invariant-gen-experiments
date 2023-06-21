int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  int x6;
  int x7;
  // pre-conditions
  (x1 = x3);
  (x2 = x4);
  // loop body
  while ((x3 != 0)) {
    {
    (x3  = (x3 - 1));
    (x4  = (x4 - 1));
    }

  }
  // post-condition
if ( (x1 == x2) )
assert( (x4 == 0) );

}
