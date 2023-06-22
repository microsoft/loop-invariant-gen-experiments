 #include "myassert.h"

int __BLAST_NONDET;

void main() {
  int i,j,k,l,n,m;

  if(j<=n+k); else goto END;
  for (i=0;i<n;i++) {
    for(i=0;i<m;i++){
      j=k;
      if(__BLAST_NONDET) 
	for(l=0;l<n;l++) j++;
    }
    if (k > 5 ) {
      for(l=0;l<m;l++){
	
      }
      for(l=0;l<m;l++){
	for (j = 0;j<n+k;j++);
      }
    } else if ( k > n ) {
      for(l=0;l<n;l++) j--;
    }
  }
  __VERIFIER_assert(j<=n+k);
 END:;
}
