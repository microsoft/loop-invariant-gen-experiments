#include "seahorn/seahorn.h"
extern int unknown();


int main() {
int a = unknown();
int m = unknown();
int j = unknown();
int k = unknown();

    j = 0;
    k = 0;

    while ( k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    sassert( a <= m);
}
