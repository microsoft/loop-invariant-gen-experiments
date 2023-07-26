# 1 "/tmp/tmp.6E3V4HoYk8.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.6E3V4HoYk8.c"
extern void __VERIFIER_error();
extern void __VERIFIER_assume(int cond);
void __VERIFIER_assert(int /*@  predicates{cond!=0} predicates_tpl{0==0} @*/ cond){
  if(!(cond)){
    ERROR: __VERIFIER_error();
  }
  return;
}
extern int __VERIFIER_nondet_bool();
extern int __VERIFIER_nondet_int();
void foo()
{
  int y=0;
  int /*@  predicates{c1!=0,c1==0} @*/ c1=__VERIFIER_nondet_bool(), /*@  predicates{c2!=0,c2==0} @*/ c2=__VERIFIER_nondet_bool();
  if(c1)y++;
  if(c2)y--;
  else y+=10;
}
int main()
{
  int d = 1;
  int /*@  predicates{(x>=(-1000000)),x<=0,x<=1000000,x>0} @*/ x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x <= 1000000 && x >= -1000000);
  int /*@  predicates{c1!=0,c1==0} @*/ c1=__VERIFIER_nondet_bool(), /*@  predicates{c2!=0,c2==0} @*/ c2=__VERIFIER_nondet_bool();
  if(c1)d = d - 1;
  if(c2)foo();
  c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();
  if(c1)foo();
  if(c2)d = d - 1;
  while(x>0)
  {
    x=x-d;
  }
  __VERIFIER_assert(x<=0);
}
