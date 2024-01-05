/*

Commit Number: 5ff623fc990210e4bb5dc04447f9e95ad83e5195
URL: https://github.com/alsa-project/alsa-lib/commit/5ff623fc990210e4bb5dc04447f9e95ad83e5195
Project Name: alsa-lib
License: LGPL-2.1
termination: FALSE
*/
int main()
{
    unsigned int best = __VERIFIER_nondet_uint();
    unsigned int pre;
    unsigned int cur;
    unsigned int st_max = __VERIFIER_nondet_uint();
    unsigned int it_min = __VERIFIER_nondet_uint();
    if( st_max <= it_min )
        return 0;
    if( best == 0 )
        return 0;
    for( cur = best ;  ; cur += best )
    {
        if( st_max < cur )
        break;
        if( it_min > cur  )
        continue;
    }
    return 0;
}
