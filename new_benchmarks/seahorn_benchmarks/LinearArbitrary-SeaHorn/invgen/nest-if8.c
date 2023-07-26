 #include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int i,j,k,n,m;
  m = unknown ();
  n = unknown ();
  if( m+1 < n ); else goto END;
  for ( i=0; i<n; i+=4 ) {
    for ( j=i; j<m; ) {
      if ( unknown() ){
	sassert( j >= 0 );
	j++;
	k = 0;
	while( k < j ) {
	  sassert( k < n );
	  k++;
	}
	
      }
      else { 
	sassert( n+j+5>i );
	j+= 2;
      }
    }


  }
 END:;
}
