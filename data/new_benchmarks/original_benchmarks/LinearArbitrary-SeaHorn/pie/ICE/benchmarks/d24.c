#include "seahorn/seahorn.h"

int main(int argc, char* argv[]) {
  int i, j, k, n;

  j = unknown ();
  k = unknown ();
  n = unknown ();

  for (i = 0; i < n; i++) {
    for (j = i; j < n; j++) {
      for (k = j; k < n; k++) {
        sassert(k >= i);
      }
    }
  }

  sassert(1);
  return 0;
}
