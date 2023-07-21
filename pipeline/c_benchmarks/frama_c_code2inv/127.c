#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

int main() {
  // variable declarations
  int i;
  int j;
  int x;
  int y;
  int z1;
  int z2;
  int z3;
  // pre-conditions
  (i = x);
  (j = y);
  // loop body
  while ((x != 0)) {
    {
    (x  = (x - 1));
    (y  = (y - 1));
    }

  }
  // post-condition
if ( (y != 0) )
assert( (i != j) );

}
