extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
/*
 * These two programs differ in the number of iterations of the
 * loop. This versions does one more iteration with n = 0, while
 * the other version adds one to the output value.
 *
 * Do they compute the same?
 * No, not in general.
 * But they do for non-negative integers. That's why there is
 * the precondition in the second release. Drop it and you'll
 * get a counterexample (n=-1, e.g.)
 */
void main() {
	int n0=unknown(),n1=n0,n2=n0;
   int m1 = 0, m2 = 0;

   while((n1 >= 0)) { // <--- loop condition n>=0
      m1++;
      n1--;
   }

   while((n2 > 0)) { // <--- loop condition n>0
      m2++;
      n2--;
   }
   assert(n0<0 || m1==m2+1);
}
