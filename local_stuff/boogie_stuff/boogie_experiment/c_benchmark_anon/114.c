int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x1 = 0);
  (x2 = 0);
  // loop body
  while (unknown()) {
    {
    (x2  = (x2 + 1));
    (x1  = (x1 + 1));
    }

  }
  // post-condition
if ( (x1 != x2) )
assert( (x1 == -1) );

}
