 #include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int i,j,k,n;

  tmpl("(le(n,i,j,k),le(n,i,j,k))");
  
  for (i=0;i<n;i++)
    for (j=i;j<n;j++)
      for (k=j;k<n;k++)
	if(unknown()){
	  sassert(k>=j);
	  sassert(j>=i);
	  //	  assert(i>=0);
	}
}
