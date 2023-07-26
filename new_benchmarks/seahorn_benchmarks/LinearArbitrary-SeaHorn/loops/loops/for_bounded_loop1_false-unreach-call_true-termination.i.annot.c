# 1 "/tmp/tmp.6E3V4HoYk8.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.6E3V4HoYk8.c"
extern void __VERIFIER_error();

extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int /*@  predicates{cond!=0} predicates_tpl{0==0} @*/ cond){
  if(!(cond)){
    ERROR: __VERIFIER_error();
  }
  return;
}

int __VERIFIER_nondet_int();

int main(){
  int /*@  predicates{i>=0} @*/ i=0, /*@  predicates{x!=0,x<=i,x==0,x>=i} terms_tpl{x-i} @*/ x=0, /*@  predicates{y!=0,y==0} @*/ y=0;
  int /*@  predicates{n!=0,n==0,n>0,n>=i,n>i} @*/ n=__VERIFIER_nondet_int();
__VERIFIER_assume(n>0);
  for(i=0; i<n; i++)
  {
    x = x-y;
    __VERIFIER_assert(x==0);
    y = __VERIFIER_nondet_int();
__VERIFIER_assume(y!=0);
    x = x+y;
    __VERIFIER_assert(x!=0);
  }
  __VERIFIER_assert(x==0);
}
