/*
Commit Number: cea58cb6d8fe0d27bfcbab57776bd36d5c724ec3
URL: https://github.com/GNOME/evolution-data-server/commit/cea58cb6d8fe0d27bfcbab57776bd36d5c724ec3
Project Name: evolution-data-server
License: GPL2
termination: false


*/
int strcspn(const char *strSrc, const char *str)
{
    const char *s;
    const char *t = strSrc;
    while (*t != '\0')
    {
        s = str;
        while (*s != '\0')
        {
            if (*t == *s )
            return t-strSrc;
            ++s;
        }
        ++t;
    }
    return 0;
}
int main()
{
    char buf[100];
    for( int i = 0 ; i < 99 ; i++ )
        buf[i] = __VERIFIER_nondet_char();
    buf[99] = '\0';
    char *p = buf;
    while( *p )
    {
        int len = strcspn( p , "\n");
        p += len;
    }
    return 0;

}
