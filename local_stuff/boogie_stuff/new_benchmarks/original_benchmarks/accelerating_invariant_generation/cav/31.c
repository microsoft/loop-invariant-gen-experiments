
int unknown1(){
    int x; return x;
}


/*
 * "nest-if8" from InvGen benchmark suite
 */


int main() {
  int i,j,k,n,m;
  if( m+1 > n - 1 )
     return;
  for ( i=0; i<=n-1; i+=4 ) {
    for ( j=i; j<=m-1; ) {
      if (unknown1()){
	if(j <= -1)
	  goto ERROR;
	if(j < 0)
	  return;
        j++;
        k = 0;
        while( k < j ) {
          k++;
        }
      }
      else { 
	if(n + j + 5 <= i)
          goto ERROR;
        if(n + j + 5 < i+1)
	  return;
	j+= 2;
      }
    }
    if(j < m)
      return;
  }
  return;
 bad:;
 ERROR:;

}
