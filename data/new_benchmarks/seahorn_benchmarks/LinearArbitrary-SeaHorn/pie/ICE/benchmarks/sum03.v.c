void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
//#define a (2)
#define a (1)
unsigned int __VERIFIER_nondet_uint();

int main() { 
  int sn=0;
  unsigned int loop1=__VERIFIER_nondet_uint(), n1=__VERIFIER_nondet_uint();
  unsigned int x=0;
  int v1, v2, v3;

  while(1){
    sn = sn + a;
    x++;
    __VERIFIER_assert(sn==x*a || sn == 0);
    v1 = __VERIFIER_nondet_int();
    v2 = __VERIFIER_nondet_int();
    v3 = __VERIFIER_nondet_int();
  }
}

