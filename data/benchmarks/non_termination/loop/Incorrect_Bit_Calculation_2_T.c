/*
Commit Number: c44da115063bfea7ef8b2afd1c9d52737e2b7f70
URL: https://github.com/coreutils/coreutils/commit/c44da115063bfea7ef8b2afd1c9d52737e2b7f70
Project Name: coreutils
License: GPL3
termination: TRUE
*/
int main()
{
    int a0 = __VERIFIER_nondet_int();
    int a1 = __VERIFIER_nondet_int();
    if( ( a0 | a1 ) == 0 )
        return 0;
    while( ( a0 & 1 ) == 0)
    {
        a0 = ( a1 << 31 ) | ( a0 >> 1 );
        a1 = a1 >> 1;
    }
    return 0;
}
