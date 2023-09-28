 #include "myassert.h"

int __BLAST_NONDET;

void main() {
  int i,j,k,n,m;
  if( m+1 < n ); else goto END;
  for ( i=0; i<n; i+=4 ) {
    for ( j=i; j<m; ) {
      if ( __BLAST_NONDET ){
	__VERIFIER_assert( j >= 0 );
	j++;
	k = 0;
	while( k < j ) {
	  __VERIFIER_assert( k < n );
	  k++;
	}
	
      }
      else { 
	__VERIFIER_assert( n+j+5>i );
	j+= 2;
      }
    }


  }
 END:;
}
