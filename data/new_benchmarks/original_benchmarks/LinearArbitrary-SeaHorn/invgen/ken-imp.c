extern void __VERIFIER_error();

extern int unknown();

void main() {
  int i = unknown();
  int j = unknown();
  int x = i;
  int y = j;
  while(x!=0) {
	x--;
	y--;
  }
  if(i==j)
	if(y != 0) ERROR: __VERIFIER_error();
}
