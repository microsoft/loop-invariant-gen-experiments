# 1 "/tmp/tmp.6E3V4HoYk8.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.6E3V4HoYk8.c"
extern void __VERIFIER_error();
void __VERIFIER_assert(int /*@  predicates{cond!=0} predicates_tpl{0==0} @*/ cond){
  if(!(cond)){
    ERROR: __VERIFIER_error();
  }
  return;
}
extern unsigned int __VERIFIER_nondet_uint();
int main(){
  int /*@  predicates{sn==0} @*/ sn=0;
  unsigned int loop1=__VERIFIER_nondet_uint(), n1=__VERIFIER_nondet_uint();
  unsigned int /*@  predicates{(sn==(x*2)),x<=sn,x>=sn} terms_tpl{2*x-sn} @*/ x=0;
  while(1){
      if(x<10){
          sn = sn +(2);
      }
      x++;
      __VERIFIER_assert(sn==x*(2)|| sn == 0);
  }
}
