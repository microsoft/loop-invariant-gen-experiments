int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  int x6;
  // pre-conditions
  (x1 = 0);
  assume((x4 >= 0));
  assume((x4 >= 127));
  (x5 = (36 * x4));
  // loop body
  while (unknown()) {
    if ( (x1 < 36) )
    {
    (x5  = (x5 + 1));
    (x1  = (x1 + 1));
    }

  }
  // post-condition
if ( (x1 < 36) )
assert( (x5 < 4608) );
}