
/*
 * Initializes all elements of a to a linear function of iteration number.
 */

//@ requires size > 0;
void main(int* a, int c, int size)
{
  int i;
  for(i=0; i<size; i++) 
  {
	a[i] =2*i+c;
  }

  for(i=0; i<size; i++)
  {
	assert(a[i] ==2*i+c);
  }
}

