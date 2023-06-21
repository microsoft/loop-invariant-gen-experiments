#include "myassert.h"

int nondet_int();

/* Example from Figure 1 (a) */
void main () {

int x,y;

x=0;
y=0;

while (nondet_int()) {
x++;
y++;
}

while (x > 0 || x < 0) {
x--;
y--;
}

__VERIFIER_assert(y >= 0 && y <= 0);

} 
