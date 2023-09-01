void assert(int cond) {if (!cond) __VERIFIER_error();}
int unknown() {int x; return x;}

main(){
  int i,n,x, NONDET;

  x=0;
  i=0;
  while (i<n) {
    if (unknown() >0){
      assert(!( x>0 ));
    }
    else{
      x = 1;
    }
    i++;
  }
}
