extern void abort(void);
extern int __VERIFIER_nondet_int();
extern _Bool __VERIFIER_nondet_bool();
extern char __VERIFIER_nondet_char();
extern double __VERIFIER_nondet_double();
extern float __VERIFIER_nondet_float();
extern unsigned long __VERIFIER_nondet_ulong();
extern unsigned long long __VERIFIER_nondet_ulonglong();
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum_by_3_abstracted.c", 3, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int SIZE = 20000001;
unsigned int __VERIFIER_nondet_uint();
int main() {
  unsigned int n,i,k;
  n = __VERIFIER_nondet_uint();
  if (!(n <= SIZE)) return 0;
  i = 0;
  // START NAIVELOOPABSTRACTION
  if (i < n) {
  i = __VERIFIER_nondet_uint();
  if (!(i < n)) abort();
  if( i < n ) {
      i = i + 1;
    }
  if (i < n) abort();
  }
  // END NAIVELOOPABSTRACTION
  int j = i;
  while( j < n ) {
    j = j+1;
  }
  k = j;
  while( k < n ) {
    k = k+1;
  }
  __VERIFIER_assert((i+j+k)/3 <= SIZE);
  return 0;
}

