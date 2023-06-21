#include "seahorn/seahorn.h"
extern int unknown();

int main() {
int n = unknown();
int y = unknown();
    int x = 1;

    while (x <= n) {
        y = n - x;
        x = x +1;
    }

    if (n > 0) {
        sassert (y >= 0);
        //sassert (y <= n);
    }
}
