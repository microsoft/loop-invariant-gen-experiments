/* extended Euclid's algorithm */

int gcd (int x, int y)
pre( x>0 && y>0 ); 
    {
    int a,b,p,q,r,s;

    a=x;
    b=y;
    p=1;
    q=0;
    r=0; 
    s=1;

    inv( GCD(a,b)==GCD(x,y) && a==y*r+x*p && b==x*q+y*s );
    while( b!=0 ) 
        { 
        int c,quot;

        c=a;
        quot=0;

        inv( a == quot*b+c && GCD(a,b) == GCD(x,y) && a==y*r+x*p && b==x*q+y*s );
        while( c>=b )
            {
            c=c-b;
            quot=quot+1;
            }
        a=b;
        b=c;
            {
            int temp;

            temp=p;
            p=q;
            q=temp-q*quot;
            temp=r;
            r=s;
            s=temp-s*quot;
            } 
        }

    assert( GCD(x,y)==y*r+x*p );

    return a;
    }
post( result==GCD(x,y) );