extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

/*
 * Adapted from http://www.sanfoundry.com/c-programming-examples-arrays/
 * C Program to Find the Largest Number in an Array
 */

int SIZE;
int main()
{
	SIZE = __VERIFIER_nondet_int();
	int i;
	int largest[1];
	int array[SIZE];

	for(i = 0; i < SIZE; i++) 
	{
		array[i] = __VERIFIER_nondet_int();
	}

	for (i = 0; i < SIZE; i++)
	{
		if(i == 0) {
			largest[0] = array[0];
		} else {
			if (largest[0] < array[i])
				largest[0] = array[i];
		}
	}

	int x;
	for ( x = 0 ; x < SIZE ; x++ ) {
		__VERIFIER_assert(  largest[0] >= array[ x ]  );
	}

	return 0;
}
