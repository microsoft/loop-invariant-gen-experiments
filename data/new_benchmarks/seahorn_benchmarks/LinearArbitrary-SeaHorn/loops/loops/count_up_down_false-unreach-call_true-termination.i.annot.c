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

int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int /*@  predicates{x<=n,x>0,x>=0} @*/ x=n, /*@  predicates{y!=n,y<=x,y==n,y>=x} terms_tpl{y+x} @*/ y=0;
  while(x>0)
  {
    x--;
    y++;
  }
  __VERIFIER_assert(y!=n);
}
