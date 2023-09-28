/*
Commit Number: f61813eaea814b49489b3e917c6bdb850c7aeb8b
URL: https://github.com/open-quantum-safe/libssh/commit/f61813eaea814b49489b3e917c6bdb850c7aeb8b
Project Name: libssh
License: GPL-2.0
termination: TRUE
*/
int main()
{
    int needed =  __VERIFIER_nondet_int();
    int smallest = 1;
    while( smallest <= needed )
    {
        if( smallest == 0 )
            return 0;
        smallest <<= 1;
    }
    return 0;
}
