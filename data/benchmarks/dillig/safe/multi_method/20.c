
void memcpy(void*_dest, void* _source, int bytes)
{
	char* dest = (char*) _dest;
	char* source = (char*) _source;
	int i;
	for(i=0; i<bytes; i++) 
	{
		dest[i] = source[i];
	}
}

void check_memcpy(char* source, int size)
{
	char* buf = malloc(sizeof(char)*size);
	memcpy(buf, source, size);
	int i;
	for(i=0; i<size; i++)
	{
		static_assert(buf[i] == source[i]);
	}	
}

