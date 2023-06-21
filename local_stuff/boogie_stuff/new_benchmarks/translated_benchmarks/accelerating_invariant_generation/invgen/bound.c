int main() {
  int n,h;
  int i,j,k,m;

  assume(n >=0 );
  assume(n <=200); 
  k=0;
  i=n;
  h = i+k;
  while( i > 0 ){
    i--;
    k++;
    h = i+k;
  }

  j = k;
  m = 0;
  h = j+m;
  while( j > 0 ) {
	j--;
	m++;
	h = j+m;
  }
  assert(i >= 0 );
}
/*
bound_vars(vars(n)).

bound_exp(pc(main-1-11), i+k).
bound_exp(pc(main-10-18),j+m).

bound_var(data(V1, V5, V2, V4, V3),V4).
bounding_vars(data(V1, V5, V2, V4, V3),[V1]).

*/
