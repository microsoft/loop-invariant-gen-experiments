int main()
{
	int n;
	n = unknown_int();

	int i, j, k, l;
	assume(l > 1);

	i = n;
	while (i >= 1)
	{ // Accumulation of right-hand transformations.
		if (i < n)
		{
			if (unknown())
			{
				j = l;
				while (j <= n)
				{
					assert(1 <= j);
					j++;
				}
				j = l;
				while (j <= n)
				{
					k = l;
					while (k <= n)
					{
						k++;
					}
					j++;
				}
			}
			j = l;
			while (j <= n)
			{
				j++;
			}
		}
		l = i;
		i--;
	}
}
