int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  // pre-conditions
  (x1 = 0);
  assume((x2 >= 0));
  assume((x3 >= 0));
  assume((x2 >= x3));
  // loop body
  while (unknown()) {
    if ( (x1 < x3) )
    {
    (x1  = (x1 + 1));
    }

  }
  // post-condition
if ( (x1 < x3) )
assert( (0 <= x1) );
}