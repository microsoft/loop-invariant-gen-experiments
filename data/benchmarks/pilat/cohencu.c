/* printing consecutive cubes, by Cohen */

void cubes(int N) 
pre( true );
    {

    int n,x,y,z;

    n=0;   x=0;   y=1;   z=6;

    inv(  z == 6*n + 6   &&   y == 3*n^2 + 3*n + 1   &&   x == n^3  );
    while( n<=N )
        {
        assert(  x == n^3  );

        write_int(x);
        n=n+1;
        x=x+y;
        y=y+z;
        z=z+6;
        }
    }

post( true );