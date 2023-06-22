/* integer division algorithm, by Cohen */

int division (int x, int y)
pre( x >= 0 && y > 0 );
    {
    int q,r;

    q=0;
    r=x;

    inv( x==q*y+r && r >= 0 );
    while( r>=y )
        {

        int d,dd;

        d=1;
        dd=y;

        inv( r>=y*d && dd==y*d && x==q*y+r && r>=0 ); 
        while ( r>= 2*dd ) 
            {
            d = 2*d;
            dd = 2*dd;
            }
        r=r-dd;
        q=q+d;
        }

    assert( q==x/y );

    return r;
    }
post( result == x % y);