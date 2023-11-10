 #include "myassert.h"

int __BLAST_NONDET;

// This is an iterative version of merge sort.
// It merges pairs of two consecutive lists one after another.
// After scanning the whole array to do the above job,
// it goes to the next stage. Variable k controls the size
// of lists to be merged. k doubles each time the main loop
// is executed.
#include <stdio.h>
#include <math.h>
int i,n,t,k;
int l,r,u,j;
int x,y,z;
//int a[100000],b[100000];

main()
{ 
  x=1;
  while (x<n) {
    z=1;
    while (z+x<=n) {
      y=z+x*2;
      if (y>n) y=n+1;
      //      merge(z,z+x,y);
      l = z; r = z+x; u = y;
      i=l; j=r; k=l;
      while (i<r && j<u) { 
	//	__VERIFIER_assert(0<=i);__VERIFIER_assert(i<=n);
	//__VERIFIER_assert(0<=j);__VERIFIER_assert(j<=n);
	if(__BLAST_NONDET) {
	//if (a[i]<=a[j]) {
	  //__VERIFIER_assert(0<=i);__VERIFIER_assert(i<=n);
	  //__VERIFIER_assert(0<=k);__VERIFIER_assert(k<=n);
	  //b[k]=a[i]; 
	  i++;
	} 
	else {
	  //__VERIFIER_assert(0<=j);__VERIFIER_assert(j<=n);
	  //__VERIFIER_assert(0<=k);__VERIFIER_assert(k<=n);	  
	  //b[k]=a[j]; 
	  j++;
	}
	k++;
      }
      //__VERIFIER_assert(0<=r);__VERIFIER_assert(r<=n);
      
      __VERIFIER_assert(k<=n);
      
      while (i<r) {
	//__VERIFIER_assert(0<=i);__VERIFIER_assert(i<=n);
	//__VERIFIER_assert(0<=k);__VERIFIER_assert(k<=n);
	//b[k]=a[i]; 
	i++; 
	k++;
      }
      while (j<u) { 
	//__VERIFIER_assert(0<=j);__VERIFIER_assert(j<=n);
	//__VERIFIER_assert(0<=k);__VERIFIER_assert(k<=n);
	//b[k]=a[j]; 
	j++; k++;
      }
      for (k=l; k<u; k++) { 
	//__VERIFIER_assert(0<=k);__VERIFIER_assert(k<=n);
	//a[k]=b[k]; 
      }
      
      z=z+x*2;
    }
    x=x*2;
  }
}

/*
main()
{ printf("input size \n");
  scanf("%d",&n); 
  for (i=1;i<=n;i++) a[i]=random()%1000;
  t=clock();
  sort1();
  for (i=1;i<=10;i++) printf("%d ",a[i]);
  printf("\n");
  printf("time= %d millisec\n",(clock()-t)/1000);
}
*/
