int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x2 = 0);
  (x1 = 1);
  // loop body
  while ((x1 <= 8)) {
    {
    (x1  = (x1 + 1));
    (x2  = (x2 + 1));
    }

  }
  // post-condition
if ( (x2 != 8) )
assert( (x2 == 0) );

}
