#include "myassert.h"

#include <math.h>
//#include "nrutil.h"

int NONDET;

int n;

int nondet_int();

void main()
{

  n = nondet_int();

  int i,j,k,l;
  
  //  tmpl("(le(n,l,i,j,k),le(n,l,i,j,k))")
  tmpl("(le(n,l,i,j,k))");

  assume(l>1);

  for (i=n;i>=1;i--) { // Accumulation of right-hand transformations. 
    if (i < n) {
      if ( NONDET ) {
	for (j=l;j<=n;j++) { // Double division to avoid possible underflow. 
	  tmpl("(le(n,l,i,j,k),le(n,l,i,j,k))");
	  __VERIFIER_assert(1<=j);
	  //__VERIFIER_assert(j<=n);
	  // __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	  // __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=m); // TODO feasible counterexample found, hm
	  //__VERIFIER_assert(1<=l);__VERIFIER_assert(l<=n);
	}
	for (j=l;j<=n;j++) {
	  
	  for (k=l;k<=n;k++) { 
	    //__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=m); // TODO feasible counterexample found, hm
	    //__VERIFIER_assert(1<=k);__VERIFIER_assert(k<=n);
	    //__VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	  }

	  /*	  for (k=l;k<=n;k++) { 
	    //__VERIFIER_assert(1<=k);__VERIFIER_assert(k<=n);
	    //__VERIFIER_assert(1<=j);	    
	    //__VERIFIER_assert(j<=n);
	    //__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	    }*/
	}
      }
      for (j=l;j<=n;j++) { 
        //__VERIFIER_assert(1<=j);
	//__VERIFIER_assert(j<=n);
	//__VERIFIER_assert(1<=i);
	//__VERIFIER_assert(i<=n);
      }
    }
    
    //__VERIFIER_assert(1<=i);
    //__VERIFIER_assert(i<=n);
    //__VERIFIER_assert(1<=i);
    //__VERIFIER_assert(i<=n);
    l=i;
  }
}
