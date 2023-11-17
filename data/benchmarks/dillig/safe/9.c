
/*
 * Copies num_to_copy number of elements of b to a.
 */
/*@
requires size > 0;
requires num_to_copy > 0;
requires \separated(a+(0..size-1), b+(0..size-1));
*/
void main(int* a, int*b,  int size, int num_to_copy)
{
  assume(num_to_copy <= size);
  int i;
  for(i=0; i<num_to_copy; i++) 
  {
	a[i] = b[i];
  }

  for(i=0; i<num_to_copy; i++)
  {
	assert(a[i] == b[i]);
  }

}

