#include "myassert.h"

int nondet_int();

int main () {

int x;
int y;
int xa = 0;
int ya = 0;

while (nondet_int()) {
	x = xa + 2*ya;
	y = -2*xa + ya;

	x++;
	if (nondet_int()) y	= y+x;
	else y = y-x;

	xa = x - 2*y;
	ya = 2*x + y;
}

__VERIFIER_assert(xa + 2*ya >= 0);
return 0;
}

