/* algorithm for computing the product of two natural numbers */

int prod (int a,int b)
pre( a >= 0 && b >= 0 ); 
    {
    int x,y,z;

    x = a;
    y = b;
    z = 0;

    inv( z+x*y==a*b );
    while( y!=0 ) 
        { 
        if ( y % 2 ==1 )
            {
            z = z+x;
            y = y-1;
            }
        x = 2*x;
        y = y/2;
        }
    return z; 
    }
post( result==a*b );