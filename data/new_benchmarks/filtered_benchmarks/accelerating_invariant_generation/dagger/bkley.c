// This example is adapted from StIng
int main()
{

	int invalid;
	int unowned;
	int nonexclusive;
	int exclusive;

	if (!(exclusive == 0))
		return;
	if (!(nonexclusive == 0))
		return;
	if (!(unowned == 0))
		return;
	if (!(invalid >= 1))
		return;

	while (unknown())
	{
		if (unknown())
		{
			if (!(invalid >= 1))
				return;
			nonexclusive = nonexclusive + exclusive;
			exclusive = 0;
			invalid = invalid - 1;
			unowned = unowned + 1;
		}
		else
		{
			if (unknown())
			{
				if (!(nonexclusive + unowned >= 1))
					return;
				invalid = invalid + unowned + nonexclusive - 1;
				exclusive = exclusive + 1;
				unowned = 0;
				nonexclusive = 0;
			}
			else
			{
				if (!(invalid >= 1))
					return;
				unowned = 0;
				nonexclusive = 0;
				exclusive = 1;
				invalid = invalid + unowned + exclusive + nonexclusive - 1;
			}
		}
	}

	assert(exclusive >= 0);
	assert(unowned >= 0);
	assert(invalid + unowned + exclusive + nonexclusive >= 1);
}

// LI computed is
// exclusive >= 0 && unowned >= 0 &&  nonexclusive >= 0 && invalid + unowned + exclusive >= 1 &&
// 2*invalid + unowned + 2*exclusive >= 1