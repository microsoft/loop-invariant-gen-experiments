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
  unsigned int i=0;
  int /*@  predicates{x!=0,x==0} @*/ x=0, /*@  predicates{y==0} @*/ y=0;
  int /*@  predicates{n>0} @*/ n=__VERIFIER_nondet_int();
__VERIFIER_assume(n>0);
  for(i=0; 1; i++)
  {
    __VERIFIER_assert(x==0);
  }
  __VERIFIER_assert(x!=0);
}
