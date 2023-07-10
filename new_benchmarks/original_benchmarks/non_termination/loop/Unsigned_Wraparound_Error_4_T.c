/*
Commit Number: ce9d4462423ac74a1dbbc4ce52c2c81cfcdda766
URL: https://github.com/ArtifexSoftware/mupdf/commit/ce9d4462423ac74a1dbbc4ce52c2c81cfcdda766
Project Name: mupdf
License: AGPL-3.0
termination: TRUE
*/
int main()
{
    unsigned int n = __VERIFIER_nondet_uint();
    while( n > 0 )
    {
        unsigned int len = n;
        if( len > 16 )
            len = 16;
        n -= len;
    }
    return 0;
}
