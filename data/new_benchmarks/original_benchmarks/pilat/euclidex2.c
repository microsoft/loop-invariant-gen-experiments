/* extended Euclid's algorithm */

int gcd (int x, int y)
pre(  x > 0  &&  y > 0   ); 
    {
    int a,b,p,q,r,s;

    a=x;
    b=y;
    p=1;
    q=0;
    r=0;
    s=1;

    inv(    GCD(a,b) == GCD(x,y)    &&    a == y*r + x*p    &&    b == x*q + y*s    );
    while(a!=b) 
        { 

        if (a>b) {a = a-b; p = p-q; r=r-s;}

        else {b = b-a; q = q-p; s = s-r;}

        }

    assert(   GCD(x,y) == y*r + x*p   );

    return a;
    }
post(   result==GCD(x,y)   );