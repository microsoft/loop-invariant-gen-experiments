#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

int main() {
  // variable declarations
  int i;
  int j;
  int x;
  int y;
  // pre-conditions
  (j = 0);
  (i = 0);
  (y = 1);
  // loop body
  while ((i <= x)) {
    {
    (i  = (i + 1));
    (j  = (j + y));
    }

  }
  // post-condition
if ( (y == 1) )
assert( (i == j) );

}
