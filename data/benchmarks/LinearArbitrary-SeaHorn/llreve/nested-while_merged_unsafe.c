extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int x0=unknown(), x1=x0, x2=x0, g0=unknown(), g1=g0, g2=g0;
  int i1 = 0, i2 = 0;
  while ((i1 < x1)) {
    i1 = i1 + 1;
    g1 = g1 - 2; // <--- g is decremented by 1 in total
    g1 = g1 + 1;
    while((x1 < i1)) {
      x1 = x1 + 2;
      x1 = x1 - 1;
      g1 = g1 + 1;
    }
  }
//	assert(x1<0 || g1==g0-x0);

  while ((i2 < x2)) {
    i2 = i2 + 1;
    g2 = g2 - 2; // <--- g is decremented by 2
    while((x2 < i2)) {
      x2 = x2 + 1;
      g2 = g2 + 2;
    }
  }
//	assert(x0<0 || g2==g0-2*x0);
	assert(g1==g2);
}
