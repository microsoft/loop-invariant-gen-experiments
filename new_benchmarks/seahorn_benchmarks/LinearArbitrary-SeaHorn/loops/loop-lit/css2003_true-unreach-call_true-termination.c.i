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
    int i,j,k;
    i = 1;
    j = 1;
    k = __VERIFIER_nondet_int();
    if (!(0 <= k && k <= 1)) return 0;
    while (i < 1000000) {
 i = i + 1;
 j = j + k;
 k = k - 1;
 __VERIFIER_assert(1 <= i + k && i + k <= 2 && i >= 1);
    }
    return 0;
}
