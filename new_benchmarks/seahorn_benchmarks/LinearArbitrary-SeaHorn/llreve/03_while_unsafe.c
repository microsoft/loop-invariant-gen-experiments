extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
int f1(int n, int c) {
   int i;
   int j;
   int x;

   i = 0;
   j = 0;
   x = 0;

   while(i < n) {
      j = 5*i + c;
      x = x + j;
      i++;
   }
   return x;
}

/*
 * Change one character to remedy the regression!
 */

int f2(int n, int c) {
   int i;
   int j;
   int x;

   i = 0;
   j = 0;
   x = 0;

   while(i < n) {
      x = x + j;
      j = j + 5;
      i++;
   }
   return x;
}

void main()
{
	int n,c;
   n = unknown();
   c = unknown();
	int res1=f1(n,c);
	int res2=f2(n,c);
	assert(res1==res2);
}
