extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
int f1(int z) {
  int i = 0; // <--- i is assigned 0

  while (i <= 10) {
    i++;
  }
  return i;
}

int f2(int z) {
  int i = 1; // <--- i is assigned 1

  while (i <= 10) {
    i++;
  }
  return i;
}

void main()
{
	int z = unknown();
	int res1=f1(z);
	int res2=f2(z);
	assert(res1==res2);
}
