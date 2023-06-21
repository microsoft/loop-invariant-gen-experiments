int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  (x2 = x1);
  // loop body
  while ((x2 > 1)) {
    {
    (x2  = (x2 - 1));
    }

  }
  // post-condition
if ( (x1 >= 0) )
assert( (x2 == 1) );

}