#include "seahorn/seahorn.h"

extern int unknown ();

int main(int argc, char * argv[]) {
  int i = 0;
  int j = 0;

  int n = unknown ();
  if (n >= 0) {

  while (i < n) {
    i++;
    j++;
  }

  sassert(j < n + 1);
  }
}
