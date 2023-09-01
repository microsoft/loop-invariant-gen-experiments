void __VERIFIER_assume(int cond) {if (!cond) {LOOP: goto LOOP;}};
int __VERIFIER_nondet_int() {int i; return i;}
int main(){

int n = __VERIFIER_nondet_int();
int i=0;
int j=0;
int min=0;

	__VERIFIER_assume(n>=0);

	while (i < n-1) {

		min = i;

		j=i+1;

		while (j < n) {
//entry_a1:
			if( j >= n || -1 >= j || min >= n || -1 >= min )
				goto ERROR;

			if (__VERIFIER_nondet_int()) {
				min = j;
			}

			if ( i != min) {
// entry_a2:
				if( i >= n || -1 >= i || min >= n || -1 >= min )
					goto ERROR;
			}

			j=j+1;

		}

		i=i+1;
	}

	return 0;
ERROR: __VERIFIER_error();
	return -1;
}
