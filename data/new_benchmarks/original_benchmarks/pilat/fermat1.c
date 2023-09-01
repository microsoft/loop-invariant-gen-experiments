/* program computing a divisor for factorisation, by Knuth */

int fermat(int N, int R)
pre( N>=1 && (R-1)*(R-1) <N && N<=R*R && N%2==1 );
    {
    int u,v,r;
    u=2*R+1;
    v=1;
    r=R*R-N;

    inv( 4*(N+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && N>=1 ); 
    while ( r!=0 )
        {

        inv( 4*(N+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && N>=1 ); 
        while ( r>0 ) 
            {
            r=r-v;
            v=v+2;
            }

        inv( 4*(N+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && N>=1 );  
        while ( r<0 )
            {
            r=r+u;
            u=u+2;
            }
        }

    assert( u!=v );

    return((u-v)/2);
    }
post( N % result==0 );