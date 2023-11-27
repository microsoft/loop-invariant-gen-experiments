

/*
 * Swaps a and b twice and asserts that 
 * a is same as a_copy and b is same as b_copy.
 */

void swap(int* a, int* b, int size)
{
	int i;
	for(i=0; i<size; i++)
	{
		int t = a[i];
		a[i] = b[i];
		b[i] = t;
	}
}

void double_swap(int size, int* a, int* b)
{
	int i;
	int* a_copy = malloc(sizeof(int)*size);
	

	for(i=0; i<size; i++)
	{
		a_copy[i] = a[i];
	}

	int* b_copy = malloc(sizeof(int)*size);
	for(i=0; i<size; i++)
	{
		b_copy[i] = b[i];
	}
	
	swap(a, b, size);
	swap(a, b, size);	


	for(i=0; i<size; i++)
	{
		static_assert(a[i] == a_copy[i]);
		static_assert(b[i] == b_copy[i]);
	}
	
	free(a_copy);
	free(b_copy);
}

