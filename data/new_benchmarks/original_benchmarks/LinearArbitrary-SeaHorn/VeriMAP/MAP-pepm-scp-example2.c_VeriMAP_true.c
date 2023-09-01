int x = 0;
int y = 0;
int n;
extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }


void incr(int z) 
{ 
  y = y + z;
}

void main() {

  while (x < n) {
    x = x + 1; 
    incr(x); 
  }

  __VERIFIER_assert( x<=y );

}
