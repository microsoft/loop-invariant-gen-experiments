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


int main(){
  int /*@  predicates{i<=8,i>=1} @*/ i, /*@  predicates{(sn==(8*2)),sn<=i,sn==0,sn>=i} terms_tpl{sn-2*i} @*/ sn=0;
  for(i=1; i<=8; i++){
    if(i<4)
    sn = sn +(2);
  }
  __VERIFIER_assert(sn==8*(2)|| sn == 0);
}
