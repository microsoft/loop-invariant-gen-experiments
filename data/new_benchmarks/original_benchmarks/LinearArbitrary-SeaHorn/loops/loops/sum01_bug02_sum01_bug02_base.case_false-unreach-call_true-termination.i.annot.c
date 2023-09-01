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
  int /*@  predicates{i==1,i==2,i==3,i==4,i>=1} @*/ i, /*@  predicates{n>=i} @*/ n=__VERIFIER_nondet_uint(), /*@  predicates{(sn==(n*2)),sn<=i,sn==0,sn>=i} terms_tpl{sn-2*i} @*/ sn=0;
  for(i=1; i<=n; i++){
    sn = sn +(2);
    if(i==4)sn=-10;
  }
  __VERIFIER_assert(sn==n*(2)|| sn == 0);
}
