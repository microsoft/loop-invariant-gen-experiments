int main() {
    int x1, x2;
    int x3 = 1;

    while (x3 <= x1) {
        x2 = x1 - x3;
        x3 = x3 + 1;
    }

    if (x1 > 0) {
        //assert (x2 >= 0);
        assert (x2 <= x1);
    }
}