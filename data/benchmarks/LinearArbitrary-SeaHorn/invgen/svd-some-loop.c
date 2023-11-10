#include "seahorn/seahorn.h"

extern int unknown();

void main(){
int  n,m,l,i,j,k;

n = unknown();
m = unknown();
l = unknown();
i = unknown();
j = unknown();
k = unknown();

//ssume(n >= 1);
for (i=n;i>=1;i--) { // Accumulation of right-hand transformations. 
  l = i+1;
    if (i < n) {
      if ( unknown() ) {
	for (j=l;j<=n;j++) { // Double division to avoid possible underflow. 

	  sassert(1<=j);sassert(j<=n);
	  sassert(1<=i);sassert(i<=n);
	  //	  assert(1<=i);assert(i<=m); // TODO feasible counterexample found, hm
	  //assert(1<=l);assert(l<=n);
	  //  v[j][i]=(a[i][j]/a[i][l])/g;
	}
	for (j=l;j<=n;j++) {
	  // s = 0.0;
	  for (k=l;k<=n;k++) { 

	    //assert(1<=i);assert(i<=m); // TODO feasible counterexample found, hm
	    sassert(1<=k);sassert(k<=n);
	    sassert(1<=j);sassert(j<=n);
	    //  s += a[i][k]*v[k][j];
	  }
	  for (k=l;k<=n;k++) { 
	    sassert(1<=k);sassert(k<=n);
	    sassert(1<=j);sassert(j<=n);
	    sassert(1<=i);sassert(i<=n);
	    // v[k][j] += s*v[k][i];
	  }
	  }
      }
      for (j=l;j<=n;j++) { 

        sassert(1<=j);sassert(j<=n);
	sassert(1<=i);sassert(i<=n);
	//v[i][j]=v[j][i]=0.0;
	}
    }

    sassert(1<=i);sassert(i<=n);
    //    v[i][i]=1.0;
     sassert(1<=i);sassert(i<=n);
    //   g=rv1[i];
    l=i;
  }

}
