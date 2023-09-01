/*

Commit Number: fc600b6a8f0dec5642b45c1026dee24c9adb9bc2
URL: https://github.com/freedesktop/dbus/commit/fc600b6a8f0dec5642b45c1026dee24c9adb9bc2
Project Name: dbus
License: GPL2
termination: FALSE

*/
#define EINTR 1
#define OTHER 2
int errno;
int waitpid()
{
    int num = __VERIFIER_nondet_int();
    while( num < 0 )
    {
        if( __VERIFIER_nondet_int() && errno != EINTR )
            errno = EINTR;
        else
            errno = OTHER;
        return num;
    }
    return num;
}

int main()
{

    int ret = waitpid();
again:
    if( ret == 0 )
    {
        ret = waitpid();
    }
    if( ret < 0 )
        if( errno == EINTR )
        goto again;
    return 0;
}
