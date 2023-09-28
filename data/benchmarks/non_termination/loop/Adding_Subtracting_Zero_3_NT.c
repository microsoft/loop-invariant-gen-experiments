/*

Commit Number: d5396e453ff39428c38a1b5af261e4e89bd90e8f
URL: https://github.com/cmus/cmus/commit/d5396e453ff39428c38a1b5af261e4e89bd90e8f
Project Name: cmus
License: GPL-2.0
termination: false





This case is simplified by this bug from GitHub.

In C:
ssize_t read  (int fd, void *buf, size_t count);
Return the number of bytes read successfully, return -1 on error and set errno. If the end of the file has been reached before the read is adjusted, the read returns 0 this time.

This program uses arrays to rewrite read function.

In this program:
int read ( int loc, int len );
When EOF, return 0;
When abnormal, return -1;
When read, return the number of bytes read successfully.

flag: When the end of the file is reached, flag is 1; otherwise flag is 0.

This program is non-terminating because when the end of the file is reached and flag is 1, read function will always return 0, which is infinite.
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
    int pos = 0;
    int size = __VERIFIER_nondet_int();
    flag = 0;
    int errno = 0;
    if( size <= 0 || size > 65536 )
        return 0;
    while( pos < size )
    {
        int rc = read( pos, size - pos);
        if( rc == -1 )
        {
            errno++;// abnormal is OK
            if( errno == 5 )
                return 0;
            continue;
        }
        pos += rc;
    }
    return 0;
}
