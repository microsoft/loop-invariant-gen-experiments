int main()
{
    int x1 = 0;
    int x2 = 0;
    int x3;

    while (x1 < x3) {
        if (unknown()) {
            x2 = x1;
        }
        x1 = x1 + 1;
    }

    if(x3 > 0) {
       assert (x2 < x3);
       //assert (x2 >= 0);
    }
}