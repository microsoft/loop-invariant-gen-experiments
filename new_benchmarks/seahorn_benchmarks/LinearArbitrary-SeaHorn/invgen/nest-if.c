#include "seahorn/seahorn.h"


void main() {
  int i,k,n;

  n = unknown ();

  //  tmpl("(le(n,i,k,l),le(n,i,k,l))");
  tmpl("(le(n,i,k),le(n,i,k))");

  //  assume(l>0);

  for (k=1;k<n;k++){
    for (i=1;i<n;i++)
      sassert(1<=k);
    if(i<n)
      for (i=1;i<n;i++);
  }

 }
