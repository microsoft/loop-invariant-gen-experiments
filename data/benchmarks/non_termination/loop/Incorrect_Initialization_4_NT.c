/*
Commit Number: fa741cd4fffbbaa5d4ba9a15f53550ac7817cc92
URL: https://github.com/behdad/fontconfig/commit/fa741cd4fffbbaa5d4ba9a15f53550ac7817cc92
Project Name: fontconfig
License: MIT
termination: FALSE
*/
int main()
{
    int h = __VERIFIER_nondet_int();
    int hash = __VERIFIER_nondet_int();
    int rehash = __VERIFIER_nondet_int();
    if( h < 0 || hash <= 0 || rehash <= 0 || rehash > hash)
        return 0;
    int i = h % hash;
    int r;
    while( i < hash )
    {
        if( !r ) r = h % rehash;
        i += r;
    }
    return 0;
}
