#include "seahorn/seahorn.h"

void main() {
  int i,k,n,l;

  l = unknown ();
  n = unknown ();

  tmpl("(le(n,i,k,l),le(n,i,k,l))");

  if (l>0) {
  for (k=1;k<n;k++){
    for (i=l;i<n;i++){  
      sassert(1<=i);
    }
    if(unknown ())
      l = l + 1;
  }
  }
 }
