#include "myassert.h"

int nondet_int();

//This example is adapted from StIng 
int main()
{
	int x;
	int y;

	if (! (x==0)) return;
	if (! (y==0)) return;

	while (nondet_int())
	{
		if (nondet_int())
		{
			if (! (x >= 9)) return;
			x = x + 2;
			y = y + 1;
		}
		else
		{
			if (nondet_int())
			{
				if (!(x >= 7)) return;
				if (!(x <= 9)) return;
				x = x + 1;
				y = y + 3;
			}
			else
			{
				if (nondet_int())
				{
					if (! (x - 5 >=0)) return;
					if (! (x - 7 <=0)) return;
					x = x + 2;
					y = y + 1;
				}
				else
				{
					if (!(x - 4 <=0)) return;
					x = x + 1;
					y = y + 2;
				}
			}
		}
	}
	__VERIFIER_assert(-x + 2*y  >= 0);
	__VERIFIER_assert(3*x - y  >= 0);
}

