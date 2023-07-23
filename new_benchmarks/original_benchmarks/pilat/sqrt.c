/* algorithm computing the floor of the square root of a natural number */

int sqrt (int n)
pre( n >= 0 );
    {
    int a,su,t;

    a=0;
    su=1;
    t=1;

    inv(    a ^2 <= n   &&   t == 2*a + 1   &&   su == ( a + 1 ) ^2    );    
    while ( su <= n )
        {
        a=a+1;
        t=t+2;
        su=su+t;
        }

    return a;
    }
post(   result ^2 <= n    &&   ( result + 1 ) ^2 > n   );
