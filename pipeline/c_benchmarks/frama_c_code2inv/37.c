#define assume(e) if(!(e)) return 0;
extern int unknown(void);

int main() {
  // variable declarations
  int c;
  // pre-conditions
  (c = 0);
  // loop body
  while (unknown()) {
    {
      if ( unknown() ) {
        if ( (c != 40) )
        {
        (c  = (c + 1));
        }
      } else {
        if ( (c == 40) )
        {
        (c  = 1);
        }
      }

    }

  }
  // post-condition
if ( (c < 0) )
if ( (c > 40) )
{;
 //@ assert( (c == 40) );
}

}
