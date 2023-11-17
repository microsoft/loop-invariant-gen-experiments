/*
 * Copies source into dest and checks that dest has 
 * the same contents as source.
 */

void strcpy(char* dest, char* source)
{
	for(; *source!='\0'; source++, dest++)
	{
		*dest = *source;
	}
	
}
void check_strcpy(char* str1, char* str2)
{
	strcpy(str1, str2);

	for(; *str2!='\0'; str1++, str2++) {
		static_assert(*str1 == *str2);
	}
}

