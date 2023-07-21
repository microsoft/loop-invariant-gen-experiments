#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

int main() {
  // variable declarations
  int sn;
  int x;
  // pre-conditions
  (sn = 0);
  (x = 0);
  // loop body
  while (unknown()) {
    {
    (x  = (x + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != x) )
assert( (sn == -1) );

}
