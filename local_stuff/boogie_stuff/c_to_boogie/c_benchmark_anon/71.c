int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  // pre-conditions
  (x1 = 0);
  assume((x2 >= 0));
  assume((x2 >= 127));
  (x3 = (36 * x2));
  // loop body
  while (unknown()) {
    if ( (x1 < 36) )
    {
    (x3  = (x3 + 1));
    (x1  = (x1 + 1));
    }

  }
  // post-condition
if ( (x1 < 36) )
assert( (x3 >= 0) );
}