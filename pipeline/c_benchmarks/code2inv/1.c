int main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  (x = 1);
  (y = 0);
  // loop body
  /*@  
    loop invariant 1 <= x;
    loop invariant 0 <= y <= 100000;
    loop invariant x >= y;
    loop invariant 1 <= x;
    loop invariant 0 <= y <= 100000;
    loop invariant x >= y;
    loop invariant x >= y;
    loop invariant y <= 100000;
    loop invariant x >= 1;
    loop invariant y >= 0;
    loop invariant x >= y;
    loop invariant y <= 100000;
    loop invariant x >= 1;
    loop invariant y >= 0;
    loop invariant x >= 1;
    loop invariant y >= 0;
    loop invariant x >= y;
    loop invariant y <= 100000;
  */
  while ((y < 100000)) {
    {
    (x  = (x + y));
    (y  = (y + 1));
    }

  }
  // post-condition
assert( (x >= y) );
}
