int m,y;

void thr() {
  int x;
  acquire(m); // assume(m=0 /\ m'=1);
  x = 0;
  y = 0;
  x = 1;
  assert(x>=1);
  release(m); // assume(m'=0);
}
