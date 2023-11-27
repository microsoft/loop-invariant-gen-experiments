
void main(int* a, int size)
{
	int pos = -1;
	int i;
	for(i=0; i<size; i++)
	{
		if(a[i] != 0) {
			pos = i;
			break;
		}
	}
	
	if(pos !=-1) assert(a[i] !=0);
}

