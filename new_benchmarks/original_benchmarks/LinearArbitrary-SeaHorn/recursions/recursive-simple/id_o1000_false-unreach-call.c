extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error();

int id(int x) {
  if (x==0) return 0;
  return id(x-1) + 1;
}

int main(void) {
  int input = __VERIFIER_nondet_int();
  int result = id(input);
  if (result == 1000) {
    ERROR: __VERIFIER_error();
  }
}
