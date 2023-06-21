#include "seahorn/seahorn.h"
extern int unknown();

int main() {
    int d1 = 1;
    int d2 = 1;
    int d3 = 1;
    int x1 = 1;
int x2 = unknown();
int x3 = unknown();

    while( x1 > 0) {
        if(x2 > 0) {
            if(x3 > 0) {
                x1 = x1 - d1;
                x2 = x2 - d2;
                x3 = x3 - d3;
            }
        }
    }

    sassert (x2 >= 0);
    //sassert (x3 >= 0);
}
