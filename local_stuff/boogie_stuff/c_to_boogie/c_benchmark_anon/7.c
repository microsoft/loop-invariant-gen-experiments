int main() {
  // variable declarations
  int x1;
  int x2;
  // pre-conditions
  assume((x1 >= 0));
  assume((x1 <= 10));
  assume((x2 <= 10));
  assume((x2 >= 0));
  // loop body
  while (unknown()) {
    {
    (x1  = (x1 + 10));
    (x2  = (x2 + 10));
    }

  }
  // post-condition
if ( (x1 == 20) )
assert( (x2 != 0) );

}
