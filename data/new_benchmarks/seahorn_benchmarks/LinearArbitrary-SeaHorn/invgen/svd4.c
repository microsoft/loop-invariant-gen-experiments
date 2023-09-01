#include "seahorn/seahorn.h"

void main(int n)
{
  int i,j,k,l,m;
  l = unknown();
  m = unknown();
  
  //tmpl("(le(n,m,l,i,j,k))");
    //tmpl("(le(n,m,l,i,j,k),le(n,m,l,i,j,k))");

  if(!n>m)
    return;
  
  if (m<=n) { i = m; } else { i = n; } 

  for ( ;i>=1;i--) { // Accumulation of left-hand transformations. 
    l=i+1;

    sassert(1<=i);
    sassert(i<=n); 

    for (j=l;j<=n;j++) {
      sassert(1<=i);
      sassert(i<=m);
      sassert(1<=j);sassert(j<=n);
    }

    if ( unknown() ) {
      for (j=l;j<=n;j++) {
	for (k=l;k<=m;k++) {
	  sassert(1<=k);sassert(k<=m);
	  sassert(1<=i);sassert(i<=n);
	  sassert(1<=j);sassert(j<=n);
	}

	sassert(1<=i);sassert(i<=m);
	sassert(1<=i);sassert(i<=n);
	for (k=i;k<=m;k++) {
	  sassert(1<=k);sassert(k<=m);
	  sassert(1<=j);sassert(j<=n);
	  sassert(1<=i);sassert(i<=n);
	  }
      }
      for (j=i;j<=m;j++) { 
	sassert(1<=j);sassert(j<=m); 
	sassert(1<=i);sassert(i<=n);
      }
    } else for (j=i;j<=m;j++) { 
      sassert(1<=j);sassert(j<=m); 
      sassert(1<=i);sassert(i<=n);
    }
    
    sassert(1<=i);sassert(i<=m); 
    sassert(1<=i);sassert(i<=n);
    }
}
