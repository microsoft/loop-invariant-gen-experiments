int main() {
    int x1, x2, x3, x4, x5;

    assume(x1 <= x3);
    x4 = 0;
    x5 = 0;

    while (x5 < x2) {
        if(x3 < x1) {
            x3 = x1;
        }
        x5 = x5 + 1;
    }

    assert( x1 <=  x3);
}