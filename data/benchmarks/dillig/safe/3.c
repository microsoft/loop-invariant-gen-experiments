

/*
 * Initializes num_to_init number of elements of a to 0.
 */

/*@ requires size > 0;
 requires num_to_init > 0;
*/
void main(int* a, int size, int num_to_init)
{
  assume(num_to_init <= size);
  int i;
  for(i=0; i<num_to_init; i++) 
  {
	a[i] = 0;
  }

  for(i=0; i<num_to_init; i++)
  {
	assert(a[i] == 0);
  }
}

