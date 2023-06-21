int main() {
  // variable declarations
  int x1;
  int x2;
  int x3;
  int x4;
  int x5;
  // pre-conditions
  assume((x1 >= 0));
  assume((x1 <= 2));
  assume((x2 <= 2));
  assume((x2 >= 0));
  // loop body
  while (unknown()) {
    {
    (x1  = (x1 + 2));
    (x2  = (x2 + 2));
    }

  }
  // post-condition
if ( (x2 == 0) )
assert( (x1 != 4) );

}
