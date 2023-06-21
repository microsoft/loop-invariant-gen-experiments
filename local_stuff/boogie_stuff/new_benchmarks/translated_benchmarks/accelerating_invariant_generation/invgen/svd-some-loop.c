int main()
{
	int n, m, l, i, j, k;
	i = n;
	while (i >= 1)
	{ // Accumulation of right-hand transformations.
		l = i + 1;
		if (i < n)
		{
			if (unknown())
			{
				j = l;
				while (j <= n)
				{
					assert(1 <= j);
					assert(j <= n);
					assert(1 <= i);
					assert(i <= n);
					j++;
				}
				j = l;
				while (j <= n)
				{
					k = l;
					while (k <= n)
					{
						assert(1 <= k);
						assert(k <= n);
						assert(1 <= j);
						assert(j <= n);
						k++;
					}
					k = l;
					while (k <= n)
					{
						assert(1 <= k);
						assert(k <= n);
						assert(1 <= j);
						assert(j <= n);
						assert(1 <= i);
						assert(i <= n);
						k++;
					}
					j++;
				}
			}
			j = l;
			while (j <= n)
			{
				assert(1 <= j);
				assert(j <= n);
				assert(1 <= i);
				assert(i <= n);
				j++;
			}
		}

		assert(1 <= i);
		assert(i <= n);
		assert(1 <= i);
		assert(i <= n);
		l = i;
		i--;
	}
}
