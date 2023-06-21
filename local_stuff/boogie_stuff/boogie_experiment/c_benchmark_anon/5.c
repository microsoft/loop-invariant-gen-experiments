int main()
{
    int x1 = 0;
    int x2;
    int x3, x4;

    while(x1 < x2) {
       x1 += 1;
       if( x4 <= x3) {
          x3 = x4;
       }
    }

    if(x2 > 0) {
       assert (x4 >= x3);
    }
}