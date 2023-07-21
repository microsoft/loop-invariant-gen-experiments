#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

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
  while (unknown()) {
    {
    (x  = (x + 2));
    (y  = (y + 2));
    }

  }
  // post-condition
if ( (x == 4) )
assert( (y != 0) );

}
