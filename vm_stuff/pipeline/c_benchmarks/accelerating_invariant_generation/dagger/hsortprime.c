//This example is adapted from StInG 
int main()
{
	int n;
	int l;
	int r;
	int i;
	int j;

	if (! (n >= 2)) return;
	if (! (r - n == 0)) return;
	if (! (i - l ==0)) return;
	if (! (j - 2*l == 0)) return;
	if (! (2*l - n >= 0)) return;
	if (! (2*l - n - 1 <= 0)) return;

	while (unknown())
	{
		if (unknown())
		{
			if (! (r -j  -1 >= 0)) return;
			i = j + 1;
			j = 2*j + 2;
		}
		else
		{
			if (unknown())
			{
				if (! (j -r <=0)) return;
				i = j;
				j = 2*j;
			}
			else
			{
				if (unknown())
				{
					if (! (l >=2)) return;
					if (! (r  >=2)) return;
					i = l - 1;
					j = 2 *l - 2;
					l = l - 1;
				}
				else
				{
					if (! (l <= 1)) return;
					r = r - 1;
					if (! (r >=3)) return;
					i = l;
					j = 2*l;
				}
			}
		}
	}
	assert(-2*l + r + 1 >= 0);
	return;
}

// LI computed is
// 2*i - j = 0 &&
// -2*l + r >= -1 &&
// -2*l + 3*r - 2*i >= 0 && 
// -l + i >= 0 && 
// r >= 2 &&
// l >= 1 &&
// n - r >= 0
