#include "myassert.h"

int nondet_int();

//This example is adapted from StInG 
int main()
{
	int x1;
	int v1;
	int x2;
	int v2;
	int x3;
	int v3;
	int t;

	x1=100;
	x2=75;
	x3=-50;
	if (! (v3 >= 0)) return;
	if (! (v1 <= 5)) return;
	if (! (v1 -v3 >= 0)) return;
	if (! (2* v2 - v1 - v3 == 0)) return;
	t=0;

	if (! (v2 +5 >=0)) return;
	if (! (v2 <= 5)) return;
	while (nondet_int())
	{
		if (! (v2 +5 >=0)) return;
		if (! (v2 <= 5)) return;
		if (nondet_int())
		{
			if (! (2* x2 - x1 - x3>=0)) return;
			x1 = x1+v1;
			x3 = x3+v3;
			x2 = x2+v2;
			v2 = v2-1;
			t = t+1;
		}
		else
		{
			if (! (2*x2 -x1-x3 <=0)) return;
			x1 = x1+v1;
			x3 = x3+v3;
			x2 = x2+v2;
			v2 = v2+1;
			t = t+1;
		}
	}
	__VERIFIER_assert(v1 <= 5);
	__VERIFIER_assert(2*v2 + 2*t  >= v1 + v3);
	__VERIFIER_assert(5*t  + 75 >= x2);
	__VERIFIER_assert(v2 <= 6);
	__VERIFIER_assert(v3  >= 0);
	__VERIFIER_assert(v2 + 6 >= 0);
	__VERIFIER_assert(x2 + 5*t >= 75);
	__VERIFIER_assert(v1 - 2*v2 + v3 + 2*t >= 0);
	__VERIFIER_assert(v1 - v3 >= 0);
}

