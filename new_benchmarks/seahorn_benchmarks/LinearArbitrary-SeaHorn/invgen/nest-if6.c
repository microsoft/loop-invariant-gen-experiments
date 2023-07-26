 #include "seahorn/seahorn.h"

extern int unknown();

void main()
//REAL a[];

{
  int lda,n;
  //REAL t;
  int j,k,kp1,l,nm1;
  int i, itemp;

  n = unknown ();
  lda = unknown ();

  if( n < lda); else goto END; 
  if( 0 <= n ); else goto END; 
//*info = 0;
  nm1 = n - 1;
  if (nm1 >=  0) {
    for (k = 0; k < nm1; k++) {
      kp1 = k + 1;
     
      /* find l = pivot index	*/
      //l = idamax(n-k,&a[lda*k+k],1) + k;
     
      int dx = k;
      int incx = 1;

      //REAL dmax;

      
      if( n-k < 1 ) { itemp = -1; goto IDAMAXEND; }
      if(n-k ==1 )  { itemp = 0; goto IDAMAXEND; }
      if(incx != 1) {
	
	/* code for increment not equal to 1 */
	
	int ix = 1;
	//dmax = fabs((double)dx[0]);
	//assert(0 <= dx);//assert(dx < lda);
	ix = ix + incx;
	for (i = 1; i < n-k; i++) {
	  //assert(0 <= dx+ix);assert(dx+ix < lda);
	  //if(fabs((double)dx[ix]) > dmax)  {
	  if(unknown()) {
	    itemp = i;
	    //assert(0 <= dx+ix);assert(dx+ix < lda);
	    //dmax = fabs((double)dx[ix]);
	  }
	  ix = ix + incx;
	}
      }
      else {
	
	/* code for increment equal to 1 */
	
	itemp = 0;
	// dmax = fabs((double)dx[0]);
	for (i = 1; i < n-k; i++) {
	  //assert(0 <= dx+i);assert(dx+i < lda);
	  //if(fabs((double)dx[i]) > dmax) {
	  if(unknown()) {
	    itemp = i;
	    //assert(0 <= dx+i);assert(dx+i < lda);
	    //dmax = fabs((double)dx[i]);
	  }
	}
      }

    IDAMAXEND:  l = itemp +k;


      //ipvt[k] = l;
      
      /* zero pivot implies this column already 
	 triangularized */
      //assert(0 <= k);assert(k < lda);
      //assert(0 <= l);assert(l < lda);
      //if (a[lda*k+l] != ZERO) {
      if ( unknown() ) {
	/* interchange if necessary */
	
	if (l != k) {
	  // t = a[lda*k+l];
	  // a[lda*k+l] = a[lda*k+k];
	  // a[lda*k+k] = t; 
	}
	
	/* compute multipliers */
	
	//t = -ONE/a[lda*k+k];
	// dscal(n-(k+1),t,&a[lda*k+k+1],1);
	
	/* row elimination with column indexing */
	
	for (j = kp1; j < n; j++) {
	  //assert(0 <= j);assert(j < lda);
	    //assert(0 <= l);assert(l < lda);
	    //assert(0 <= k);assert(k < lda);
	  //t = a[lda*j+l];
	  if (l != k) {
	    // a[lda*j+l] = a[lda*j+k];
	    // a[lda*j+k] = t;
	  }
	  //daxpy(n-(k+1),t,&a[lda*k+k+1],1,
	  //&a[lda*j+k+1],1);
	} 
      }
      else { 
	//*info = k;
      }
    } 
  }
   sassert(0 <= n);sassert(n < lda);

 END:;  //ipvt[n-1] = n-1;
  
  //if (a[lda*(n-1)+(n-1)] == ZERO) *info = n-1;
}















/*
void main() {
  int i,j,k,n;

  for (i=0;i<n;i++)
    for (j=i;j<n;j++)
      if(NONDET){ 
	assert(j>=0);
	assert(n>i); 
      }
}
*/
