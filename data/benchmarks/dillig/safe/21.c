
/*
 * Looks for a certain element in array and sets
 * pos to the index of this element. 
 */
void main(int* a, int size, int elem)
{
	int i;
	int pos = -1;
	for(i=0; i<size; i++)
	{
		if(a[i] == elem) 
		{
			pos = i;
			break;
		}
	}
	if(pos!= -1) assert(a[pos] == elem);	


}

