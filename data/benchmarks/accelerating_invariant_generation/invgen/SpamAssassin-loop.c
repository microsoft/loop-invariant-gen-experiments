#include "myassert.h"

int __BLAST_NONDET;

void main ()
{
  int len;
  int i;
  int j;
  //  char buffer[BUFSZ];
  int bufsize;
  int limit = bufsize - 4;

  tmpl("(le(len,i,bufsize,j,limit),le(len,i,bufsize,j,limit))");

  for (i = 0; i < len; ) {
    for (j = 0; i < len && j < limit; ){     
      if (i + 1 < len){ 
	__VERIFIER_assert(i+1<len);//1
	__VERIFIER_assert(0<=i);//2//Interesting assert
	if( __BLAST_NONDET ) goto ELSE;
        __VERIFIER_assert(i<len);//3
	__VERIFIER_assert(0<=i); //4
        __VERIFIER_assert(j<bufsize);//5 //Interesting Assert
	__VERIFIER_assert(0<=j);	
	//        buffer[j] = msg[i];
        j++;
        i++;
        __VERIFIER_assert(i<len);//6
	__VERIFIER_assert(0<=i);//7
        __VERIFIER_assert(j<bufsize);//8 //Very intersting
	__VERIFIER_assert(0<=j);	//9

	//        buffer[j] = msg[i];
        j++;
        i++;
        __VERIFIER_assert(j<bufsize);//10
	__VERIFIER_assert(0<=j);	//11
        /* OK */
	//        buffer[j] = '.';
        j++;
      } else {
ELSE:
        __VERIFIER_assert(i<len);//12
	__VERIFIER_assert(0<=i);//Really really interesting
        __VERIFIER_assert(j<bufsize);//13
	__VERIFIER_assert(0<=j);	//14
	
	//	buffer[j] = msg[i];
        j++;
        i++;
      }
    }
  }
}


