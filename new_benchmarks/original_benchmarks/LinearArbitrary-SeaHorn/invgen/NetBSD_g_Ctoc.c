#include "seahorn/seahorn.h"

extern int unknown();

int main ()
{
  int BASE_SZ = unknown();
  int __BLAST_NONDET = unknown();
  
  //  char buf [BASE_SZ];
  // char str [BASE_SZ];
  int i;
  int j;
  int len = BASE_SZ;

  if(BASE_SZ > 0 ); else goto END;

  // str [BASE_SZ-1] = 0;
  sassert( 0 <= BASE_SZ-1 );

  if (len == 0)
    goto END; 
  
  i = 0;
  j = 0;
  while (1) {
    if ( len == 0 ){ 
      goto END;
    } else {
      sassert( 0<= j ); sassert(j < BASE_SZ);
      sassert( 0<= i ); sassert(i < BASE_SZ );
      //      buf[j] = str[i];
      if ( __BLAST_NONDET ) {
        i++;
        j++;
        goto END;
      }
    }
    i ++;
    j ++;
    len --;
  }

 END:  return 0;
}

