int main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  assume((x >= 0));
  assume((x <= 2));
  assume((y <= 2));
  assume((y >= 0));
  // loop body
  /*@   
  loop invariant x % 2 == \at(x, Pre) % 2;  
  loop invariant y % 2 == \at(y, Pre) % 2;  
  loop invariant x >= 0;  
  loop invariant y >= 0;  
*/ 
  while (unknown()) {
    {
    (x  = (x + 2));
    (y  = (y + 2));
    }

  }
  // post-condition
if ( (y == 0) )
assert( (x != 4) );

}
