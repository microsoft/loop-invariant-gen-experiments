/* binary division algorithm, by Kaldewaij */

int division (int A, int B)
pre( A >= 0 && B > 0 );
    {
    int q,r,b;

    q=0;
    r=A;
    b=B;

    inv(   exists   (  int   k;   k >= 0  &&  b == 2^k*B  )   &&   q == 0   &&   r == A  &&  A >= 0  &&  B > 0  );
    while(r>=b)
        {
        b=2*b;
        }

    inv(   A == q*b + r   &&   r >= 0   &&   exists   (  int   k;   k >= 0 && b == 2^k*B  )   &&  B > 0  &&  b > r  );
    while(b!=B)
        {
        q=2*q;
        b=b/2;
        if (r>=b) 
            {
            q=q+1;
            r=r-b;
            }
        }

    assert(q==A/B);

    return r;
    }
post( result == A % B);