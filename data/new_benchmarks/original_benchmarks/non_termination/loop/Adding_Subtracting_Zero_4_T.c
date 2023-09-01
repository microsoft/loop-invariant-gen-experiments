/*
Commit Number: caa6003b6419d001593478a46fb4cbf8e502e818
URL: https://github.com/tytso/e2fsprogs/commit/caa6003b6419d001593478a46fb4cbf8e502e818
Project Name: e2fsprogs
License: GPL-2.0
termination: true
*/
int flag = 0;
int read( int loc , int len )
{
    int count = 0;
    if( flag == 1 ) //whether EOF or not
        return 0;
    while( loc < len )
    {
        int num =  __VERIFIER_nondet_int();
        if( num == 0 ) //abnormal
        {
            return -1;
        }
        else
        {
            if( num < 0 )
                num =  -num;
            num = num % 1000;
            count++;
            if( num < 995 ) //read a char
            {
                loc++;
                continue;
            }
            else // EOF
            {
                flag = 1;
                return count;
            }
        }
    }
    return count;
}
int main()
{
    int count =__VERIFIER_nondet_int();
    if( count <= 0 )
        return 0;
    int ret;
    int buf = 0;
    int tries = 0;
    while( count > 0 )
    {
        ret = read( buf, count );
        if( ret <= 0 )
        {
            if( ( ret == 0 )&& (tries++ < 5 ) )
                continue;
            return 0;
        }
        count -= ret;
        buf += ret;
    }
    return 0;
}
