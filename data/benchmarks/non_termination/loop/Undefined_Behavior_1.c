/*
Commit Number: 9b0f9003dfab6a230d46aaa94091bf509d889f37
URL: https://github.com/FFmpeg/FFmpeg/commit/9b0f9003dfab6a230d46aaa94091bf509d889f37
Project Name: FFmpeg
License: LGPL-2.1
termination: POTENTIAL FALSE
*/
int main()
{
    unsigned int num = __VERIFIER_nondet_uint();
    int bytes = 1;
    while( (num + 1 ) >> bytes * 7 )
        bytes++;
    return 0;
}
