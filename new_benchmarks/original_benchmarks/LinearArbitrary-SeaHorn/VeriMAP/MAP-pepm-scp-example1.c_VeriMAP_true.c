void __VERIFIER_assume(int cond) {if (!cond) {LOOP: goto LOOP;}};
int main(){

	int i=0;
	int k=0;
	int n = __VERIFIER_nondet_int();

	__VERIFIER_assume(n>=0);

	while (i < n) {
	   i = i + 1;
	   k = k + 2;
	}

	while (i > 0) {
	   i = i - 1;
	   k = k - 1;
	}

	if(k < n)
       goto ERROR;

	return 0;
ERROR: __VERIFIER_error();
	return -1;
}
