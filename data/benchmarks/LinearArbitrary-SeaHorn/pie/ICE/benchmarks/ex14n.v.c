extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

int main() {

    	int x,y,N, v1, v2, v3;
   	//int *a; 
   	x=1;
        N = __VERIFIER_nondet_int();
   	while (x <= N){
      		y=N-x;

		if(y < 0 || y >= N)
			__VERIFIER_assert(0 == 1);
	
		// Comment because it is unsafe as a is not even intialized.
      		//a[y] = -1;
      		x++;
		v1 = v2;
		v2 = v3;
		v3 = v1;
	
   	}

   	return 1;

}
