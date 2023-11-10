#include "seahorn/seahorn.h"

void main(int n)
{
  int i,j,k,l;
  l = unknown();
  
  if(!l>0)
  	return;

  for (i=n;i>=1;i--) { // Accumulation of right-hand transformations. 
    if (i < n) {
      if ( unknown() ) {
	for (j=l;j<=n;j++) { // Double division to avoid possible underflow.   
	  sassert(1<=j);sassert(j<=n);
	  sassert(1<=i);sassert(i<=n);
	  //assert(1<=i);assert(i<=m); // TODO feasible counterexample found
	  sassert(1<=l);sassert(l<=n);
	}
	for (j=l;j<=n;j++) {
	  for (k=l;k<=n;k++) { 
	    //assert(1<=i);assert(i<=m); // TODO feasible counterexample found
	    sassert(1<=k);sassert(k<=n);
	    sassert(1<=j);sassert(j<=n);
	  }
	  for (k=l;k<=n;k++) { 
	    sassert(1<=k);sassert(k<=n);
	    sassert(1<=j);sassert(j<=n);
	    sassert(1<=i);sassert(i<=n);
	  }
	}
      }
      for (j=l;j<=n;j++) { 
        sassert(1<=j);sassert(j<=n);
	sassert(1<=i);sassert(i<=n);
      }
    }
    
    sassert(1<=i);
    sassert(i<=n);
    sassert(1<=i);sassert(i<=n);
    l=i;
  }
}
