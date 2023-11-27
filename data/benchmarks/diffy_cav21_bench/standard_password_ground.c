extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

/*@
	requires SIZE > 0;
	requires \separated(password+(0..SIZE-1), guess+(0..SIZE-1));
*/
int main(int* password, int* guess, int SIZE)
{
	int i;
	int result[1];
	result[0] = 1;	

	for (i = 0; i < SIZE; i++)
	{
		password[i] = __VERIFIER_nondet_int();
		guess[i] = __VERIFIER_nondet_int();
	}

	for ( i = 0 ; i < SIZE ; i++ ) {
		if ( password[ i ] != guess[ i ] ) {
			result[0] = 0;
		}
	}

	int x;
	for ( x = 0 ; x < SIZE ; x++ ) {
		__VERIFIER_assert( result[0] == 0 ||  password[ x ] == guess[ x ]  );
	}
	return 0;
}
