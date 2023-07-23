/* algorithm for computing simultaneously the GCD and the LCM, by Sankaranarayanan */

int lcm (int a, int b)
pre( a>0 && b>0 ); 
    {
    int x,y,u,v;

    x=a;
    y=b;
    u=b;
    v=0;

    inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
    while(x!=y) 
        { 

        inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b ); 
        while (x>y)
            {
            x=x-y;
            v=v+u;
            }

        inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
        while (x<y)
            {
            y=y-x;
            u=u+v;
            }
        }
    return u+v;
    }
post( result == LCM(a,b) );