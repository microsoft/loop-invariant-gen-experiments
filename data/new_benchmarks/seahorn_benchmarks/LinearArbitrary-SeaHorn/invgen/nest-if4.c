#include "seahorn/seahorn.h"

void main() {
  int i,k,n,l;
  
  n = unknown ();
  l = unknown ();

  tmpl("(le(n,i,k,l),le(n,i,k,l))");

  if (l>0) {

  for (k=1;k<n;k++){
    if(unknown ())
      for (i=l;i<n;i++)
	sassert(1<=i);
    for (i=l;i<n;i++);
  }
  }
 }
