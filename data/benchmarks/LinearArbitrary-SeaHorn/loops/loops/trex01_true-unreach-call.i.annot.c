# 1 "/tmp/tmp.6E3V4HoYk8.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/tmp/tmp.6E3V4HoYk8.c"
extern void __VERIFIER_error();
extern void __VERIFIER_assume(int condition);
void __VERIFIER_assert(int /*@  predicates{cond!=0} predicates_tpl{0==0} @*/ cond){
  if(!(cond)){
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_bool();
int __VERIFIER_nondet_int();
void f(int /*@  predicates{d==1,d==2} @*/ d){
  int /*@  predicates{(x>=(-1000000)),x<=1000000} @*/ x = __VERIFIER_nondet_int(), /*@  predicates{((x>0)&&(y>0)),(y>=(-1000000)),y<=1000000} @*/ y = __VERIFIER_nondet_int(), /*@  predicates{(k>=(-1000000)),k<=1000000} @*/ k = __VERIFIER_nondet_int(), /*@  predicates{z<=y,z<k,z>=1,z>=y} terms_tpl{z-y} @*/ z = 1;
  L1:
  while(z < k){ z = 2 * z; }
  __VERIFIER_assert(z>=1);
  L2:
__VERIFIER_assume(x <= 1000000 && x >= -1000000);
__VERIFIER_assume(y <= 1000000 && y >= -1000000);
__VERIFIER_assume(k <= 1000000 && k >= -1000000);
  while(x > 0 && y > 0){
    int /*@  predicates{c!=0,c==0} @*/ c = __VERIFIER_nondet_bool();
    if(c){
      P1:
      x = x - d;
      y = __VERIFIER_nondet_bool();;
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}
int main(){
  int /*@  predicates{c!=0,c==0} @*/ c = __VERIFIER_nondet_bool();
  if(c){
    f(1);
  } else {
    f(2);
  }
  return 0;
}
