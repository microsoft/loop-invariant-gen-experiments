/*
Commit Number: 8030f9c0f092170ceb50cedf59b9c330022825b7
URL: https://github.com/aatmdev/glusterfs/commit/8030f9c0f092170ceb50cedf59b9c330022825b7
Project Name: glusterfs
License: GPL2
termination: FALSE
*/
#define EVEBT_EPOLL_SLOTS 2
int main()
{
    int EVENT_EPOLL_TABLES = 10;
    int slots_used[10];
    int ereg[10];
    int table;
    for( int i = 0 ; i < 10 ; i++ )
    {
        slots_used[i] = __VERIFIER_nondet_int();
        ereg[i] = __VERIFIER_nondet_int();
    }
    int i = 0;
    while( i < EVENT_EPOLL_TABLES )
    {
        switch( slots_used[i] )
        {
            case EVEBT_EPOLL_SLOTS:
                continue;
            case 0:
                if( !ereg[i] )
                    return 0;
                else
                    table = ereg[i];
                break;
            default:
                table = ereg[i];
                break;
        }
        if( table )
            break;
        i++;
    }
    return 0;
}
