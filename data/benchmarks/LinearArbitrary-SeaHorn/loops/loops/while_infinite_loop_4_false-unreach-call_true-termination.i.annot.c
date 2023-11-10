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

//int /*@  predicates{x==0,x==1} @*/ x=0;

int eval(int x)
{
  while(1){
      x=1;
      break;
  }
  return x;
}


int main(){
  int x = 0;
  while(1)
  {
    x = eval(x);
    __VERIFIER_assert(x==0);
  }

  __VERIFIER_assert(x==0);

  return 0;
}
