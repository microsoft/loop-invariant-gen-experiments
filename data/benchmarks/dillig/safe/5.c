
/*
 * Initializes all even elements of a to 1.
 */
//@ requires size > 0;
void main(int* a,  int size)
{
  int i;
  for(i=0; i<size; i+=2) 
  {
	a[i] = 1;
  }

  for(i=0; i<size; i+=2)
  {
	assert(a[i] == 1);
  }
}

