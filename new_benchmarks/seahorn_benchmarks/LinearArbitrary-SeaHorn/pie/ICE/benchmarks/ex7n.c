extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}


int* foo() {
   
	int x = __VERIFIER_nondet_int(), y = __VERIFIER_nondet_int();
	int* a;
   	int i, v1,v2,v3;
	int len; // Instrumented to track the size of the array
   
   	if ( x < 0 || y < 0 || y > x ) return (int *) 0;

   	//a = (int*) malloc( x * sizeof(int));
	len = x;

   	//if (a == 0 ) exit(1);
   
   	for (i=0; i < y ; ++i){
   		//a[i] = 0;
   	}

	i = 0;
	while (i < y) {
		
		if(i < 0 || i >= len)
			__VERIFIER_assert (0 == 1);
		i++;
    		v1 = __VERIFIER_nondet_int();
    		v2 = __VERIFIER_nondet_int();
    		v3 = __VERIFIER_nondet_int();
	}

   	return a;

}

int main()
{
  foo();
}
