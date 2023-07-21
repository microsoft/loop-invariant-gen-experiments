#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

int main() {
  // variable declarations
  int n;
  int v1;
  int v2;
  int v3;
  int x;
  // pre-conditions
  (x = n);
  // loop body
  while ((x > 1)) {
    {
    (x  = (x - 1));
    }

  }
  // post-condition
if ( (n >= 0) )
assert( (x == 1) );

}
