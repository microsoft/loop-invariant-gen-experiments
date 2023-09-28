extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp10.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp10.tmp.c"
# 19 "MAP/SAFE-exbench/TRACER-testwp10.tmp.c"
main(){
# 41 "MAP/SAFE-exbench/TRACER-testwp10.tmp.c"
  int x = __VERIFIER_nondet_uint();
  if (x==1){
    x++;
  }
  else{
    if (x==2){
      x++;
    }
    else{
      if(x==3){
 x++;
      }
      else
 x=0;
    }
  }

  __VERIFIER_assert(!( x>4 ));

}
