#include "seahorn/seahorn.h"

//int __BLAST_NONDET;

void main() {
  int i,j,k,n,m;
  n = unknown ();
  m = unknown (); 
  if(n<=m); else goto END;
  for (i=0;i<n;i++) 
    for (j = 0;j<n;j++)
      for (k = j; k<n+m; k++)
	sassert(i+j<=n+k+m);
 END:;
}
