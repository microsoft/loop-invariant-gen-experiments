#include "seahorn/seahorn.h"
extern int unknown();


int main()
{
int z1 = unknown();
int z2 = unknown();
int z3 = unknown();
    int x = 0;
    int m = 0;
int n = unknown();

    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    if(n > 0) {
       //sassert (m < n);
       sassert (m >= 0);
    }
}
