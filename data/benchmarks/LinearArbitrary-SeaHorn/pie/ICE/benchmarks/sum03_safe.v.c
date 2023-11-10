extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();

int main() { 
  int sn=0;
  unsigned int loop1=__VERIFIER_nondet_uint(), n1=__VERIFIER_nondet_uint();
  unsigned int x=0;
  int v1, v2, v3;

  while(1){
    sn = sn + 1;
    x++;
    __VERIFIER_assert(sn==x*1 || sn == 0);
    v1 = __VERIFIER_nondet_int();
    v2 = __VERIFIER_nondet_int();
    v3 = __VERIFIER_nondet_int();

  }
}

