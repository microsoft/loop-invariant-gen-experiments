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
unsigned int __VERIFIER_nondet_uint();
int __VERIFIER_nondet_bool();
int main()
{
  unsigned int /*@  predicates{x1==0} @*/ x1=__VERIFIER_nondet_uint(), /*@  predicates{x2<=x1,x2==0,x2>=x1} terms_tpl{x2-x1} @*/ x2=__VERIFIER_nondet_uint(), /*@  predicates{(((x1>0)&&(x2>0))&&(x3>0)),x3<=x1,x3<=x2,x3==0,x3>=x1,x3>=x2} terms_tpl{x3-x1,x3-x2} @*/ x3=__VERIFIER_nondet_uint();
  unsigned int /*@  predicates{d1==1} @*/ d1=1, /*@  predicates{d2==1} @*/ d2=1, /*@  predicates{d3==1} @*/ d3=1;
  int /*@  predicates{c1!=0,c1==0} @*/ c1=__VERIFIER_nondet_bool(), /*@  predicates{c2!=0,c2==0} @*/ c2=__VERIFIER_nondet_bool();
  while(x1>0 && x2>0 && x3>0)
  {
    if(c1)x1=x1-d1;
    else if(c2)x2=x2-d2;
    else x3=x3-d3;
    c1=__VERIFIER_nondet_bool();
    c2=__VERIFIER_nondet_bool();
  }
  __VERIFIER_assert(x1==0 || x2==0 || x3==0);
  return 0;
}
