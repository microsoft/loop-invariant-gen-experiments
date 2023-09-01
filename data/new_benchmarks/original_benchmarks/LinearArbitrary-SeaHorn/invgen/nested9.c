 #include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int i,j,k,n,l,m;
  n = unknown();
  m = unknown();
  l = unknown();
  
  if(3*n<=m+l); else goto END;
  for (i=0;i<n;i++)
    for (j = 2*i;j<3*i;j++) 
      for (k = i; k< j; k++)
	sassert( k-i <= 2*n );
 END:;
}
