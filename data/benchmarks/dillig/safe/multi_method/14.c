
/*
 * Swaps a and b and checks they are swapped by first making 
 * copies of the original a and b.
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

void check_swap(int size, int* a, int* b)
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


	for(i=0; i<size; i++)
	{
		static_assert(a[i] == b_copy[i]);
		static_assert(b[i] == a_copy[i]);
	}
	
	free(a_copy);
	free(b_copy);
}

