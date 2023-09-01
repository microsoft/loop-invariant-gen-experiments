int m,k;

void thr() {
  int x,j;
  acquire(m); // assume(m=0 /\ m'=1);
  x = 0;
  j = 0;
  k = 1;
  x = 1;
  assert(x>=j);
  release(m); // assume(m'=0);
}
