/*
 * Reverses array a and checks it is reversed for 
 * any k between 0 and size-1.
 */

/*@
	requires size > 0;
	requires \separated(a+(0..size-1), a_copy+(0..size-1));
*/
void main(int* a, int* a_copy, int size, int k)
{	
	int i;
	for(i=0; i<size; i++)
	{
		a_copy[i] = a[i];
	}
	
	for(i=0; i<size; i++)
	{
		a[i] = a_copy[size-1-i];
	}
	
	if(k>=0 && k<size)
	{
		assert(a[k] == a_copy[size-1-k]);
	}

}

