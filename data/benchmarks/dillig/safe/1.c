/*
 * Initializes all elements of a to a specified constant c.
 */

//@ requires size > 0;
void main(int* a, int c, int size)
{
  int i;
  for(i=0; i<size; i++) 
  {
	a[i] = c;
  }

  for(i=0; i<size; i++)
  {
	sassert(a[i] == c);
  }
}

