int main() { 
  int i;
  int n=unknown_int();
  assume(n>=0);
  int sn=0;
  i=1;
  while(i<=n) {
    if (i<10)
    sn = sn + 2;
    i++;
  }
  assert(sn==n*2 || sn == 0);
}
