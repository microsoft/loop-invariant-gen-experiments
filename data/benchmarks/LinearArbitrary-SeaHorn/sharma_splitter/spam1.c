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
      sassert(j>=0); 
      if (i + 1 < len){ 
	sassert(i+1<len);//1
	sassert(0<=i);//2//Interesting assert
	if( unknown() ) goto ELSE;
        sassert(i<len);//3
	sassert(0<=i); //4
        sassert(j<bufsize);//5 //Interesting Assert
	sassert(0<=j);	
	//        buffer[j] = msg[i];
        j++;
        i++;
        sassert(i<len);//6
	sassert(0<=i);//7
        sassert(j<bufsize);//8 //Very intersting
	sassert(0<=j);	//9

	//        buffer[j] = msg[i];
        j++;
        i++;
        sassert(j<bufsize);//10
	sassert(0<=j);	//11
        /* OK */
	//        buffer[j] = '.';
        j++;
      } else {
ELSE:
        sassert(i<len);//12
	sassert(0<=i);//Really really interesting
        sassert(j<bufsize);//13
	sassert(0<=j);	//14
	
	//	buffer[j] = msg[i];
        j++;
        i++;
      }
    }
  }
}


