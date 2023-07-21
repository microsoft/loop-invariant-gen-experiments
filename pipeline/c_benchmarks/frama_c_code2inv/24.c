#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

int main() {
  // variable declarations
  int i;
  int j;
  // pre-conditions
  (i = 1);
  (j = 10);
  // loop body
  while ((j >= i)) {
    {
    (i  = (i + 2));
    (j  = (j - 1));
    }

  }
  // post-condition
assert( (j == 6) );
}
