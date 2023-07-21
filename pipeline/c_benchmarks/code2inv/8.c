#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

int main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  assume((x >= 0));
  assume((x <= 10));
  assume((y <= 10));
  assume((y >= 0));
  // loop body
  /*@
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant x - y >= -10;
  loop invariant x - y <= 10;
  loop invariant x >= 0;
  loop invariant y >= 0;
  */
  while (unknown()) {
    {
    (x  = (x + 10));
    (y  = (y + 10));
    }

  }
  // post-condition
if ( (y == 0) )
assert( (x != 20) );

}
