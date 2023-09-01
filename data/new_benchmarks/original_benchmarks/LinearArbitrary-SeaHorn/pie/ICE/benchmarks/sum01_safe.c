extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}
int main() { 
  int i, n=__VERIFIER_nondet_int(), sn=0;
  for(i=1; i<=n; i++) {
    sn = sn + 1;
  }
  __VERIFIER_assert(sn==n || sn == 0);
}
