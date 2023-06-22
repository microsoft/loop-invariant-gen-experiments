#include "seahorn/seahorn.h"
extern int unknown();


int main() {
int n = unknown();
int v1 = unknown();
int v2 = unknown();
int v3 = unknown();
    int x = 1;
int y = unknown();

    while (x <= n) {
        y = n - x;
        x = x +1;
    }

    if (n > 0) {
      //sassert (y >= 0);
      sassert (y < n);
    }
}
