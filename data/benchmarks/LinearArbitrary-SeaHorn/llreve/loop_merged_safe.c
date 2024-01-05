extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int n = unknown();
  int i1 = 0; // <--- i is assigned 0
  int /*@ predicates{i1>=j1, i1<=j1} @*/ j1 = 0;
	int i2 = n; // <--- i is assigned n
  int /*@ terms_tpl{i2+j2} @*/ j2 = 0;

  while ((i1 <= n)) {
    i1++;
    j1++;
	assert(i1==j1);
  }
  
  while ((i2 >= 0)) {
    i2 = i2 - 1;
    j2++;
	assert(i2+j2==n);
  }

	assert(j1==j2);
}
