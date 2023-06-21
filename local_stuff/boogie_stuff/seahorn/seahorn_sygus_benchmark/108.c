#include "seahorn/seahorn.h"
extern int unknown();

int main() {
int a = unknown();
int c = unknown();
int m = unknown();
int j = unknown();
int k = unknown();

    assume(a <= m);
    j = 0;
    k = 0;

    while ( k < c) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    sassert( a <=  m);
}
