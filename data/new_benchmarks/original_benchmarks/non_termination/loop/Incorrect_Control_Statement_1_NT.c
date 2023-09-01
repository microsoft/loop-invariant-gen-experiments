/*
Commit Number: e6801c90311679fc0854af73da95fe58079c59f4
URL: https://github.com/FreeRADIUS/freeradius-server/commit/e6801c90311679fc0854af73da95fe58079c59f4
Project Name: freeradius-serve
License: GPL2
termination: false


*/
int main()
{
    int stop = 0;
    char array[101];
    for( int i = 0 ; i < 100 ; i++ )
        array[i] =  __VERIFIER_nondet_char();
    array[100] = 0;
    char* p = array;
    while( (*p) && (!stop) )
    {
        switch(*p){
        case '}':
            stop = 1;
            break;

        case ':':
            if( *(p+1) && (*(p+1) == '-')){
                p += 2;
                stop = 1;
            }
            break;
        default:
            p++;
        }
    }
    return 0;
}
