extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int t,c0;
  t = unknown();
  c0 = unknown();
  int c1=c0,c2=c0;
  int x1 = 0;
    int x2 = 0;

  if (0 < t) {
      while((0 < c1)) { // <--- while inside if
          x1++;
          c1--;
      }
	//assert(c0 <=0 || x1==c0);
  } else {
      while((0 < c1)) {
          x1--;
          c1--;
      }
	//assert(c0 <= 0 || x1==-c0);
  }

    while ((0 < c2)) {
        if (0 < t) { // <--- if inside while
            x2++;
        } else {
            x2--;
        }
        c2 = c2 - 1;
    }
	//assert(c0 <=0 || (c0>0 && t>0 && x2==c0) || (c0>0 && t<=0 && x2==-c0));
	assert(x1==x2);
}
