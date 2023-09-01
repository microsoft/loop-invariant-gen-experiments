 #include "seahorn/seahorn.h"

int NONDET;

void main() {
  int i,j,k,n;

  //tmpl("le(n,i,j,k)");
  tmpl("(le(n,i,j,k),le(n,i,j,k))");
  
  for (i=0;i<n;i++)
    for (j=i;j<n;j++)
      for (k=j;k<n;k++)
	sassert(k>=i);
}
