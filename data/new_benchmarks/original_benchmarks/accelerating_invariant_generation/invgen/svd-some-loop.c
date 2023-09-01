#include "myassert.h"


int NONDET;

void main(){
int  n,m,l,i,j,k;

//ssume(n >= 1);
for (i=n;i>=1;i--) { // Accumulation of right-hand transformations. 
  l = i+1;
    if (i < n) {
      if ( NONDET ) {
	for (j=l;j<=n;j++) { // Double division to avoid possible underflow. 

	  __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	  __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	  //	  __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=m); // TODO feasible counterexample found, hm
	  //__VERIFIER_assert(1<=l);__VERIFIER_assert(l<=n);
	  //  v[j][i]=(a[i][j]/a[i][l])/g;
	}
	for (j=l;j<=n;j++) {
	  // s = 0.0;
	  for (k=l;k<=n;k++) { 

	    //__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=m); // TODO feasible counterexample found, hm
	    __VERIFIER_assert(1<=k);__VERIFIER_assert(k<=n);
	    __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	    //  s += a[i][k]*v[k][j];
	  }
	  for (k=l;k<=n;k++) { 
	    __VERIFIER_assert(1<=k);__VERIFIER_assert(k<=n);
	    __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	    __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	    // v[k][j] += s*v[k][i];
	  }
	  }
      }
      for (j=l;j<=n;j++) { 

        __VERIFIER_assert(1<=j);__VERIFIER_assert(j<=n);
	__VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
	//v[i][j]=v[j][i]=0.0;
	}
    }

    __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
    //    v[i][i]=1.0;
     __VERIFIER_assert(1<=i);__VERIFIER_assert(i<=n);
    //   g=rv1[i];
    l=i;
  }

}
