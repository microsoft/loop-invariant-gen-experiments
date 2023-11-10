/*
d37b2f4794acf1b0b431110c5e1fb23d652c5962
https://github.com/acassen/keepalived/commit/d37b2f4794acf1b0b431110c5e1fb23d652c5962
termination: true
*/


char* strchr(char* str, int c) {
	for (; *str != 0; ++str) {
		if (*str == c) {
			return str;
		}
	}
	return 0;
}

int main()
{
    char in[100];
    for( int i = 0 ; i < 99 ; i++ )
        in[i] = '\n';
    char* p = in;
    in[99] = 0;
    while( *p )
    {
        char* n =strchr( p , '\n');
        if( n == 0 )
            n = p + 99;
        p = n + 1;
    }
    return 0;
}
