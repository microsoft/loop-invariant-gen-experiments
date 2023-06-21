#include "seahorn/seahorn.h"
extern int unknown();

int main() {
    int x = 1;
int y = unknown();

    while (x <= 100) {
        y = 100 - x;
        x = x +1;
    }

    sassert (y >= 0);
    //sassert (y < 100);
}
