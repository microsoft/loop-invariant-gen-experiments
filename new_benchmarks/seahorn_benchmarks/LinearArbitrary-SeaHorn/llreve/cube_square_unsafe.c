extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
int g1(int n)
{
  int r=0;
  int i=n;

  while (i > 0) {
    r = r + n;
    i--;
  }

  i=n; 
  n=r;
  r=0;

  while (i > 0) { // <--- second loop
    r = r + n;
    i--;
  }

  return r;
}

int g2(int n)
{
  int r=0;
  int i=n;

  while (i > 0) {
    r = r + n;
    i--;
  }

  return r;
}

void main()
{
	int n = unknown();
	int res1=g1(n);
	int res2=g2(n);
	assert(res1==res2);
}
