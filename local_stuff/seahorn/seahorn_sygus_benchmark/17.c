#include "seahorn/seahorn.h"
extern int unknown();

int main()
{
    int x = 1;
    int m = 1;
int n = unknown();

    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    if(n > 1) {
       sassert (m < n);
       //sassert (m >= 1);
    }
}
