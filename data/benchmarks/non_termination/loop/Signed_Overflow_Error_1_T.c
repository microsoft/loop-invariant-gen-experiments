/*
Commit Number: e7df42ab68e30588a5e32ed543b0711821daf009
URL: https://github.com/XQuartz/xorg-server/commit/e7df42ab68e30588a5e32ed543b0711821daf009
Project Name: xorg-server
License: MIT
termination: TRUE


*/
int main()
{
    long i;
    for( i = 1 ; i <= 0xFFFFFFFF ; i <<= 1 )
    {
        if( i == ( (long)1 << 31 ))
            break;
    }
    return 0;
}
