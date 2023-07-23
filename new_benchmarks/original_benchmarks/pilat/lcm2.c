/* algorithm for computing simultaneously the GCD and the LCM, by Dijkstra */

int lcm (int a, int b)
pre(  a > 0   &&   b > 0  ); 
    {
    int x,y,u,v;

    x=a;
    y=b;
    u=b;
    v=a;

    inv(   GCD(x,y) == GCD(a,b)   &&   x>0   &&   y>0   &&   x*u + y*v == 2*a*b  );
    while(x!=y) 
        { 
        if (x>y)
            {
            x=x-y;
            v=v+u;
            }
        else 
            {
            y=y-x;
            u=u+v;
            }
        }


    return (u+v)/2;
    }
post(   result == LCM(a,b)   );