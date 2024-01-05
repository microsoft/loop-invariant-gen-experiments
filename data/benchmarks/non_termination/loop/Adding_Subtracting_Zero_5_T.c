/*
Commit Number: 7a611ab32209fb3b79d662110582bc04e1c2c8b1
URL: https://github.com/gogins/csound-android/commit/7a611ab32209fb3b79d662110582bc04e1c2c8b1
Project Name: csound-android
License: GPL-2.0
termination: true
*/
typedef struct NNode{
    struct NNode * nxtact;
}INSDS;


INSDS * initLink(int n){
    INSDS* head=(INSDS*)malloc(sizeof(INSDS));
    head->nxtact=head;
    INSDS* cyclic=head;

    int i;
    for (i=2; i<=n; i++) {
        INSDS * body=(INSDS*)malloc(sizeof(INSDS));
        body->nxtact=body;
        cyclic->nxtact=body;
        cyclic=cyclic->nxtact;
    }
    cyclic->nxtact=cyclic;
    return head;
}

int main()
{
    int num = __VERIFIER_nondet_int();
    if( num <= 0 || num > 65534 )
        return 0;
    INSDS* list = initLink( num );
    INSDS* ip = list;
    while( ip != 0 )
    {
        INSDS *nxt = ip->nxtact;
        if( ip == nxt )
            break;
        ip = nxt;
    }
    return 0;
}
