/*
Commit Number: 8ddb6410edb0c4e87b4c6b9d0887868977c8eff5
URL: https://github.com/mirror/busybox/commit/8ddb6410edb0c4e87b4c6b9d0887868977c8eff5
Project Name: busybox
License: GPL2
termination: FALSE
*/
int flag = 0;
int fopen_or_warn()
{

    flag++;
    if( flag > 10 )// avoid almost-sure
        return 0;
    int i =  __VERIFIER_nondet_int();
    if( i >= 0 )
        return 0;
    else
        return i;
}
int main()
{
    int len = __VERIFIER_nondet_int();
    if( len <= 0 )
        return 0;
    int argv1[len];
    for( int i = 0 ; i < len - 1 ; i++ )
        argv1[i] = __VERIFIER_nondet_int();
    argv1[len-1] = 0;
    int* argv = argv1;
    int fp = 0;
    goto GOT_NEW_FILE;
    do{
        if( *argv > 0 )
        {
            fp = fopen_or_warn();
            if( fp == 0 )
                continue;
        }
        argv++;
GOT_NEW_FILE:
    fp++;
    }while( *argv );
    return 0;
}
