 #include "myassert.h"

int __BLAST_NONDET;

void main() {
  int i,j,k,n,l,m;
  
  if(3*n<=m+l); else goto END;
  for (i=0;i<n;i++)
    for (j = 2*i;j<3*i;j++) 
      for (k = i; k< j; k++)
	__VERIFIER_assert( k-i <= 2*n );
 END:;
}
