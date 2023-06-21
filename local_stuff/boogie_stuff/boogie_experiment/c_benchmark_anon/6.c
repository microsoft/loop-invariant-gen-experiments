int main()
{
    int x1, x2, x3;
    int x4 = 0;
    int x5;
    int x6, x7;

    while(x4 < x5) {
       x4 += 1;
       if( x7 <= x6) {
          x6 = x7;
       }
    }

    if(x5 > 0) {
       assert (x7 >= x6);
    }
}