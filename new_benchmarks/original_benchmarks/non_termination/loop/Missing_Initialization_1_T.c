/*
Commit Number: 407a3d94f566a68c7a862fcdac812bf53741af94
URL: https://github.com/FFmpeg/FFmpeg/commit/407a3d94f566a68c7a862fcdac812bf53741af94
Project Name: FFmpeg
License: LGPL-2.1
termination: TRUE
*/
int main()
{
    int res;
    int pkt = __VERIFIER_nondet_int();
    while( pkt < 10 )
    {
        res = 0;
        while( res == 0 )
        {
            res = __VERIFIER_nondet_int();
            pkt++;
            if( res == 0 )
                break;
        }
    }
    return 0;
}
