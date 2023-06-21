int main() {
    int x1 = 1;
    int x2 = 1;
    int x3 = 1;
    int x4 = 1;
    int x5, x6;

    while( x4 > 0) {
        if(x5 > 0) {
            if(x6 > 0) {
                x4 = x4 - x1;
                x5 = x5 - x2;
                x6 = x6 - x3;
            }
        }
    }

    //assert (x5 >= 0);
    assert (x6 >= 0);
}