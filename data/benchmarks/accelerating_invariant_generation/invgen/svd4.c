#include "myassert.h"

#include <math.h>
//#include "nrutil.h"

int NONDET;

int n;
int nondet_int();

void main()
{
  n = nondet_int();
  int i,j,k,l,m;
  
  //tmpl("(le(n,m,l,i,j,k))");
    tmpl("(le(n,m,l,i,j,k),le(n,m,l,i,j,k))");

  assume(n>m);
  if (m<=n) { i = m; } else { i = n; } 

  for ( ;i>=1;i--) { // Accumulation of left-hand transformations. 
    l=i+1;

    __VERIFIER_assert(1<=i);
    __VERIFIER_assert(i<=n); 

    for (j=l;j<=n;j++) {
      __VERIFIER_assert(1<=i);
      __VERIFIER_assert(i<=m);
      __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
    }

    if ( NONDET ) {
      for (j=l;j<=n;j++) {
	for (k=l;k<=m;k++) {
	  __VERIFIER_assert(1<=k);__VERIFIER_assert(k<=m);
	  __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	  __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	}

	__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=m);
	__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	for (k=i;k<=m;k++) {
	  __VERIFIER_assert(1<=k);__VERIFIER_assert(k<=m);
	  __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	  __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	  }
      }
      for (j=i;j<=m;j++) { 
	__VERIFIER_assert(1<=j);__VERIFIER_assert(j<=m); 
	__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
      }
    } else for (j=i;j<=m;j++) { 
      __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=m); 
      __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
    }
    
    __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=m); 
    __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
    }
}
