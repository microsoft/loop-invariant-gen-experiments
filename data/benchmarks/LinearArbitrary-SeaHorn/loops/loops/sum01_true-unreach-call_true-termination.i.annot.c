# 1 "/tmp/tmp.6E3V4HoYk8.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.6E3V4HoYk8.c"
extern void __VERIFIER_error();
extern void assert(int cond);
void __VERIFIER_assert(int cond){
  if(!(cond)){
    ERROR: __VERIFIER_error();
  }
  return;
}
extern int __VERIFIER_nondet_int();
int main(){
  int i, n=__VERIFIER_nondet_int(), sn=0;
assume(n < 1000 && n >= -1000);
  for(i=1; i<=n; i++){
    sn = sn +(2);
  }
  __VERIFIER_assert(sn==n*(2)|| sn == 0);
}
