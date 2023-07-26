#include "seahorn/seahorn.h"

extern int unknown();

int main(int argc, char *argv[]) {
  int n0, n1;
  int i0 = 0;
  int k = 0;
  n0 = unknown();
  n1 = unknown();

  while( i0 < n0 ) {
    //tmpl("(le(n0,n1,i0,i1,j0,j1,k),le(n0,n1,i0,i1,j0,j1,k))");
	i0++;
	k++;
  }
  int i1 = 0;
  while( i1 < n1 ) {
   //tmpl("(le(n0,n1,i0,i1,j0,j1,k),le(n0,n1,i0,i1,j0,j1,k))");
	i1++;
	k++;
  }
  int j1 = 0;
  while( j1 < n1 ) {
   //tmpl("(le(n0,n1,i0,i1,j0,j1,k),le(n0,n1,i0,i1,j0,j1,k))");
    sassert(k > 0);
    j1++;
    k--;
  }
  int j0 = 0;
  while( j0 < n0 ) {
   //tmpl("(le(n0,n1,i0,i1,j0,j1,k),le(n0,n1,i0,i1,j0,j1,k))");
    j0++;
    k--;
  }
  return 0;
}
