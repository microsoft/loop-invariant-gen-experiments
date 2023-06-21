int main() {
    int x1;
    int x2 = 0;
    assume (x1 > 0);

    while (unknown()) {
        if(x2 == x1) {
            x2 = 1;
        }
        else {
            x2 = x2 + 1;
        }
    }

    if(x2 == x1) {
        //assert( x2 >= 0);
        assert( x2 <= x1);
    }
}