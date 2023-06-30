#include "seahorn/seahorn.h"



extern int unknown();

void main ()
{
  int len = unknown();
  int i;
  int j;
  //  char buffer[BUFSZ];
  int bufsize = unknown();
  int limit = bufsize - 4;

  //tmpl("(le(len,i,bufsize,j,limit),le(len,i,bufsize,j,limit))");

  for (i = 0; i < len; ) {
    for (j = 0; i < len && j < limit; ){     
      if (i + 1 < len){ 
	//assert(i+1<len);//1
	//assert(0<=i);//2//Interesting assert
	if( unknown() ) goto ELSE;
        //assert(i<len);//3
	//assert(0<=i); //4
        //assert(j<bufsize);//5 //Interesting Assert
	//assert(0<=j);	
	//        buffer[j] = msg[i];
        j++;
        i++;
        //assert(i<len);//6
	//assert(0<=i);//7
        // assert(j<bufsize);//8 //Very intersting
	//assert(0<=j);	//9

	//        buffer[j] = msg[i];
        j++;
        i++;
        //assert(j<bufsize);//10
	//assert(0<=j);	//11
        /* OK */
	//        buffer[j] = '.';
        j++;
      } else {
ELSE:
        //assert(i<len);//12
	sassert(0<=i);//Really really interesting
        //assert(j<bufsize);//13
	//assert(0<=j);	//14
	
	//	buffer[j] = msg[i];
        j++;
        i++;
      }
    }
  }
}


