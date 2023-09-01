/* program for computing square roots, by Zuse */

float z3sqrt (float a, float err)
pre( a>= 1 && err > 0 );
    {
    float r,q,p,e;

    r = a-1;
    q = 1;
    p = 1/2;

    inv( q^2 + 2*r*p == a && err > 0 && p >= 0 && r >= 0 );
    while ( 2*p*r >= e )
        {
        if ( 2*r-2*q-p >= 0 )
            {
            r = 2*r-2*q-p;
            q = q+p;
            p = p/2;
            }
        else
            {
            r = 2*r;
            p = p/2;
            }
        }

        return q;
    }
post( q^2 >= a && q^2+err < a );