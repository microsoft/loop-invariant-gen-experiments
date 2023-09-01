/*
Commit Number: b00a4fa78779ff0f304fa6cb34d49622679c86d4
URL: https://github.com/anlaneg/elfutils/commit/b00a4fa78779ff0f304fa6cb34d49622679c86d4
Project Name: elfutils
License: GPL3
termination: TRUE

*/
unsigned int ffs( unsigned int w )
{
    unsigned int i = 1;
    while( w % 2 == 0 )
    {
        i++;
        w = w / 2;
    }
    return i;
}
int main()
{
    unsigned int w = __VERIFIER_nondet_uint();

    while( w != 0 )
    {
        unsigned int n = ffs(w);
        if( n < 32 )
            w >>= n;
        else
            w = 0;
    }
    return 0;
}
