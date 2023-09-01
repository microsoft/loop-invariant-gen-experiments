/*
Commit Number: 78574a66b5b286e26839877640592980de089d64
URL: https://github.com/XQuartz/xorg-server/commit/78574a66b5b286e26839877640592980de089d64
Project Name: xorg-server
License: MIT
termination: FALSE
*/
int main()
{
    int i,j;
    int num_crtc = __VERIFIER_nondet_int();
    int num_output = __VERIFIER_nondet_int();
    if( num_crtc > 65534 || num_output > 65534 )
        return 0;
    for( i = 0 ; i < num_crtc ; i++ )
    {
        for( i = 0 ; i < num_output ; i++ )
        {
            //do other
        }
    }
    return 0;
}
