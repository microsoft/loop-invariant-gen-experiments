extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
  ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();
int main() {
    int n = __VERIFIER_nondet_int();
    int m = __VERIFIER_nondet_int();
    int k = 0;
    int i,j;
    if (!(LARGE_INT <= n && n <= LARGE_INT)) return 0;
    if (!(LARGE_INT <= m && m <= LARGE_INT)) return 0;
    for (i = 0; i < n; i++) {
 for (j = 0; j < m; j++) {
     k ++;
 }
    }
    __VERIFIER_assert(k >= LARGE_INT);
    return 0;
}
