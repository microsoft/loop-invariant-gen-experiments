#include "seahorn/seahorn.h"
extern int unknown();

int main() {
    int i = 0;
int j = unknown();
int c = unknown();
int t = unknown();

    while( unknown() ) {
        if(c > 48) {
            if (c < 57) {
                j = i + i;
                t = c - 48;
                i = j + t;
            }
        }
    } 
    sassert (i >= 0);
}
