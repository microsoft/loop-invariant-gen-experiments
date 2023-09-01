void __VERIFIER_assume(int cond) {if (!cond) {LOOP: goto LOOP;}};
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
int main(){
int y = __VERIFIER_nondet_uint();
int x=0;

    __VERIFIER_assume(y>=0);

	while ( x < 10000) {
		y = y + 1;
		x = x + 1;
	}

	if( y + x < 10000)		
		goto ERROR;

	return 0;
ERROR: __VERIFIER_error();
	return -1;
}
