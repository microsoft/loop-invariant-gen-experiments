extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}
//#define a (2)
#define a (1)
//#define SIZE 8
int main() { 
  int i, sn=0;
  int SIZE = __VERIFIER_nondet_int();
  int v1, v2, v3;
  for(i=1; i<=SIZE; i++) {
    sn = sn + a;
    v1 = __VERIFIER_nondet_int();
    v2 = __VERIFIER_nondet_int();
    v3 = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(sn==SIZE*a || sn == 0);
}

