extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

int main() {

    	int x,y,N;
   	int *a; 
   	x=1;
        N =  __VERIFIER_nondet_int();
   	while (x <= N){
      		y=N-x;

		if(y < 0 || y >= N)
			__VERIFIER_assert(0 == 1);

		//Comment because it is unsafe given that a is not initialized.
      		//a[y] = -1;
      		x++;
	
   	}

   	return 1;

}
