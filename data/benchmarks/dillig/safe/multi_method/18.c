
/*
 * Checks strlen returns buffer_size(str)-1. 
 * It's not buffer_size(str) because buffer_size
 * includes the last '\0'.
 */
unsigned int strlen(char* str)
{
	int i=0;
	while(str[i] != '\0')
	{
		i++;
	}
	return i;
	
}
void check_strlen(char* str)
{
	unsigned int size = strlen(str);
	static_assert(size == buffer_size(str)-1);
}

