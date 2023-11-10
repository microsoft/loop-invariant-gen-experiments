extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

int main() { 
  int n = __VERIFIER_nondet_int(), k, i, j;

  k = 0;
  i = 0;

  while(i < n)
  {
        i = i + 1;
        k = k + 1;
  }
  j = n;
  while(j > 0)
  {
  	__VERIFIER_assert(k > 0);
	j = j - 1;
   	k = k - 1;
  }
}

