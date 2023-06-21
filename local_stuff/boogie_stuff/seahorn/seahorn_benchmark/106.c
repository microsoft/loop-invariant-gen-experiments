#include "seahorn/seahorn.h"
extern int unknown();

int main() {
int a = unknown();
int m = unknown();
int j = unknown();
int k = unknown();

    assume(a <= m);
    assume(j < 1);
    k = 0;

    while ( k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    sassert( a >= m);
}
