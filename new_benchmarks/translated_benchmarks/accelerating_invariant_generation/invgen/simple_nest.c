int main() {
  int n,m;
  int i = 1;
  m = 10;
  while( i < n ) {
    while( m > 0 ) {
      m--;
      i = 2*i;
    }
  }
  assert(i > 0 );
}
