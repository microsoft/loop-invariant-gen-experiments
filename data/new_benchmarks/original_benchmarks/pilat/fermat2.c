/* program computing a divisor for factorisation, by Bressoud */

int fermat(int N, int R)
pre(  N >= 1  &&   (R-1) ^2 < N   &&   N <= R^2  &&  N%2 == 1  );
    {
    int u,v,r;
    

    u=2*R+1;
    v=1;
    r=R*R-N;

    inv(   4*(N + r) == u^2 - v^2 - 2*u + 2*v   &&   v%2 == 1   &&   u%2 == 1   &&   N >= 1  );
    while (r!=0)
        {
        if (r>0) 
            {
            r=r-v;
            v=v+2;
            }
        else
            {
            r=r+u;
            u=u+2;
            }
        }

    assert(u!=v);
    return((u-v)/2);
    }
post(N % result==0);