#define assume(e) if(!(e)) return 0;
extern int unknown(void);

int main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  (x = 1);
  // loop body
  while ((x < y)) {
    {
    (x  = (x + x));
    }

  }
  // post-condition
{;
 //@ assert( (x >= 1) );
}
}
