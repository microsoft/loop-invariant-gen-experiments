/*
Commit Number: d37b2f4794acf1b0b431110c5e1fb23d652c5962
URL: https://github.com/acassen/keepalived/commit/d37b2f4794acf1b0b431110c5e1fb23d652c5962
Project Name: keepalived
License: GPL-2.0
termination: false

*/
int matroska_deliver_packet( int q )
{
    if( q == 1 )
        return 0;
    else
        return 1;
}
int flag = 0;
int res_return()
{
    if( flag++ < 100 )
        return __VERIFIER_nondet_int();
    return -1;
}
int main()
{
    int matroska =  __VERIFIER_nondet_int();
    int res = 0;
    while( matroska_deliver_packet( matroska) )
    {
        while( res == 0 )
        {
            int id =  __VERIFIER_nondet_int();
            switch( id ){
                case 1:
                    if( res = res_return() < 0 )
                        break;
                    if( res = res_return() == 0 )
                        res = 1;
                    break;

                default:
                case 2:
                    res = res_return();
                    break;
            }
        }
        if( res == -1 )
            matroska = 1;
    }
    return 0;
}
