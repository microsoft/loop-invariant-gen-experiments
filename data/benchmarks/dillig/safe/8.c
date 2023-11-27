

/*
 * Copies elements of b to a.
 */
/*@ requires size > 0;
 requires \separated(a+(0..size-1), b+(0..size-1));
 */
void main(int* a, int*b,  int size)
{
  int i;
  for(i=0; i<size; i++) 
  {
	a[i] = b[i];
  }

  for(i=0; i<size; i++)
  {
	assert(a[i] == b[i]);
  }
}

