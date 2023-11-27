/*@
	requires size > 0;
	requires \separated(a+(0..size-1), b+(0..size-1), res+(0..size-1));
*/
void main(int* res, int* a, int*b, int size)
{
	int i;
	for(i=0; i < size; i+=2)
	{
		res[i] = a[i];
	}
	for(i=1; i < size; i+=2)
	{
		res[i] = b[i];
	}
	int k;
	if( k>=0 && k<size) {
		if(k%2 == 0) assert(res[k] == a[k]);
		else assert(res[k] == b[k]);
	}
}

