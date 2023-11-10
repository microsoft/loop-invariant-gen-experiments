#include "seahorn/seahorn.h"

void main(int n)
{
  int i,j,k,l;
  l = unknown();
  
  //  tmpl("(le(n,l,i,j,k),le(n,l,i,j,k))")
  //tmpl("(le(n,l,i,j,k))");

  if(!l>1)
  	return;

  for (i=n;i>=1;i--) { // Accumulation of right-hand transformations. 
    if (i < n) {
      if ( unknown() ) {
	for (j=l;j<=n;j++) { // Double division to avoid possible underflow. 
	  //tmpl("(le(n,l,i,j,k),le(n,l,i,j,k))");
	  sassert(1<=j);
	  //assert(j<=n);
	  // assert(1<=i);assert(i<=n);
	  // assert(1<=i);assert(i<=m); // TODO feasible counterexample found, hm
	  //assert(1<=l);assert(l<=n);
	}
	for (j=l;j<=n;j++) {
	  
	  for (k=l;k<=n;k++) { 
	    //assert(1<=i);assert(i<=m); // TODO feasible counterexample found, hm
	    //assert(1<=k);assert(k<=n);
	    //assert(1<=j);assert(j<=n);
	  }

	  /*	  for (k=l;k<=n;k++) { 
	    //assert(1<=k);assert(k<=n);
	    //assert(1<=j);	    
	    //assert(j<=n);
	    //assert(1<=i);assert(i<=n);
	    }*/
	}
      }
      for (j=l;j<=n;j++) { 
        //assert(1<=j);
	//assert(j<=n);
	//assert(1<=i);
	//assert(i<=n);
      }
    }
    
    //assert(1<=i);
    //assert(i<=n);
    //assert(1<=i);
    //assert(i<=n);
    l=i;
  }
}
