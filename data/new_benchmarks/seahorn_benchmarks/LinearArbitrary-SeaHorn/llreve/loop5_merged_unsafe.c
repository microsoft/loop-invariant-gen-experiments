extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int n = unknown();
  int i1 = 0; // <--- i is assigned 0
  int j1 = 0;
  while (i1 < n + n) {
    j1++;
    i1++;
  }

  int i2 = n + 1; // <--- i is assigned n+1
  int j2 = 0;
  while (i2 > 0) {
    j2 = j2 + 2;
    i2 = i2 - 1;
  }

	assert(j1==j2);
}
