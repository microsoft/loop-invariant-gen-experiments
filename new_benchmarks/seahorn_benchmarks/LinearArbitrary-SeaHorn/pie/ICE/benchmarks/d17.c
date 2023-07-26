#include "seahorn/seahorn.h"

int main(int argc, char * argv[]) {
  int i, j, k, n;

  n = unknown ();

  k = 1;
  i = 1;
  j = 0;

  while (i <= n - 1) {
    j = 0;
    while (j <= i - 1) {
      k += (i - j);
      j++;
    }

    i++;
  }

  sassert(k > n - 1);
}
