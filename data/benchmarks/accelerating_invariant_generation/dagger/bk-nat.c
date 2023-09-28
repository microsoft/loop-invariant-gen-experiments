#include "myassert.h"

int nondet_int();

//This example is adapted from StIng 
int main()
{
	int invalid;
	int unowned;
	int nonexclusive;
	int exclusive;

	if (! (exclusive==0)) return;
	if (! (nonexclusive==0)) return;
	if (! (unowned==0)) return;
	if (! (invalid>= 1)) return;

	while (nondet_int())
	{
		if (nondet_int())
		{
			if (! (invalid >= 1)) return;
			nonexclusive=nonexclusive+exclusive;
			exclusive=0;
			invalid=invalid-1;
			unowned=unowned+1;
		}
		else
		{
			if (nondet_int())
			{
				if (! (nonexclusive + unowned >=1)) return;
				invalid=invalid + unowned + nonexclusive-1;
				exclusive=exclusive+1;
				unowned=0;
				nonexclusive=0;
			}
			else
			{
				if (! (invalid >= 1)) return;
				unowned=0;
				nonexclusive=0;
				exclusive=1;
				invalid=invalid+unowned+exclusive+nonexclusive-1;
			}
		}
	}

	__VERIFIER_assert(exclusive >= 0);
	__VERIFIER_assert(nonexclusive >= 0);
	__VERIFIER_assert(unowned >= 0);
	__VERIFIER_assert(invalid >= 0);
	__VERIFIER_assert(invalid + unowned + exclusive >= 1);
}

// LI that we compute is :
// unowned >= 0 && invalid >= 0 && exclusive >= 0 && nonexclusive >= 0
// && invalid + unowned + exclusive >= 1

