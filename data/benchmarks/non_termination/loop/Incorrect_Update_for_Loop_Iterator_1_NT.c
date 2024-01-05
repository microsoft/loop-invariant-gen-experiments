/*
Commit Number: bf1257b40dcac15cb7bb48ba809775885449a5e8
URL: https://github.com/radarsat1/liblo/commit/bf1257b40dcac15cb7bb48ba809775885449a5e8
Project Name: liblo
License: LGPL-2.1
termination: FALSE

*/
int main()
{
    int max_msg_size = __VERIFIER_nondet_int();
    int buffer_read_offset = __VERIFIER_nondet_int();
    int buffer_bytes_left = __VERIFIER_nondet_int();
    if( max_msg_size < -1 || buffer_read_offset <= 0 || buffer_bytes_left < 0 )
        return 0;
    int size = 64;
    while( buffer_bytes_left < size / 2)
    {
        size *= 2;
        if( max_msg_size != -1 && size > max_msg_size )
            size = max_msg_size;
        buffer_bytes_left = size - buffer_read_offset;
    }
    return 0;
}
