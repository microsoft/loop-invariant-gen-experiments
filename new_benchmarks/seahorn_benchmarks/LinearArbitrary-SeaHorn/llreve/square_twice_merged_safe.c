extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
  int n = unknown();
  int r1=0;
  int i1=n;

  while (i1 > 0) {
    r1 = r1 + n;
    i1--;
  }

  r1=0;
  int r2=0;
  i1=n;
  int i2=n;

  while (1) {
	if (i1 > 0) {  // <--- second loop
       r1 = r1 + n;
       i1--;
    }
    if (i2 > 0) {
       r2 = r2 + n;
       i2--;
    }
    assert(r1 == r2);
  }
}
