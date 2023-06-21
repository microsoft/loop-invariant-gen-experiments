#include "myassert.h"

int nondet_int();

/* Example from Figure 2 */
void main () {

int x, y, z, w;
x=y=z=w=0;


while (nondet_int() ) {

if (nondet_int()) {x++; y = y+2;}
else if (nondet_int()) {
	if (x >= 4) {x++; y = y+3; z = z+10; w = w+10;}
}
else if (x >= z && w > y) {x = -x; y = -y; }

}

__VERIFIER_assert(3*x >= y);
}
