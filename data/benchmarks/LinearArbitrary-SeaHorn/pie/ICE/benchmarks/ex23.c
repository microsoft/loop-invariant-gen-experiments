extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

int x[4608];

//pre: true
int main() {
   
	int y = __VERIFIER_nondet_int();
	int counter = 0;
	int z = __VERIFIER_nondet_int();

   	if ( 127 < y) return 0;
   	if ( y < 0) return 0;
   	z = y * 36;
   
   	while (counter < 36){

		if(z < 0 || z >= 4608)
			__VERIFIER_assert( 0 == 1 );

      		x[z] = 0;
      		z++;
      		counter++;
   	}

   	return 1;

}
