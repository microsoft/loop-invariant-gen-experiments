int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
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
if ( (x3 != x2) )
assert( (x3 == 0) );

}
