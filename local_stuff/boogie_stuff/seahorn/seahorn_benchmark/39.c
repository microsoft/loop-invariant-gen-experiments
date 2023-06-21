#include "seahorn/seahorn.h"
extern int unknown();

int main() {
int n = unknown();
    int c = 0;
    assume (n > 0);

    while (unknown()) {
        if(c == n) {
            c = 1;
        }
        else {
            c = c + 1;
        }
    }

    if(c == n) {
        //sassert( c >= 0);
        sassert( c <= n);
    }
}
