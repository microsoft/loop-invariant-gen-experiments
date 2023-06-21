/* Wensley's algorithm for real division */

float division (float P, float Q, float E)
pre(   Q > P  &&  P >= 0  &&  E > 0   );
    {
    float a,b,d,y;

    a=0;
    b=Q/2;
    d=1;
    y=0;

    inv(   a == Q*y   &&   b == Q*d/2   &&   P/Q - d < y   &&   y <= P/Q   );
    while( d>= E)
        {
        if (P< a+b)
            {
            b=b/2;
            d=d/2;
            }
        else
            {
            a=a+b;
            y=y+d/2;
            b=b/2;
            d=d/2;
            }
        }
return y;
}
post(   P/Q >= result   &&   result > P/Q - E   );