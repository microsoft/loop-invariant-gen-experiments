# 1 "/tmp/tmp.6E3V4HoYk8.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.6E3V4HoYk8.c"
extern void __VERIFIER_error();
extern void __VERIFIER_assume();
void __VERIFIER_assert(int /*@  predicates{cond!=0} predicates_tpl{0==0} @*/ cond){
  if(!(cond)){
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();
int __VERIFIER_nondet_bool();
int main(){
    int /*@  predicates{x<100,x>=100} @*/ x=__VERIFIER_nondet_int();
    int /*@  predicates{y<=0,y<=1000000,y>0} @*/ y=__VERIFIER_nondet_int();
__VERIFIER_assume(y <= 1000000);
    if(y>0){
        while(x<100){
            x=x+y;
        }
    }
    __VERIFIER_assert(y<=0 ||(y>0 && x>=100));
    return 0;
}
