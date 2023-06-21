int main() {
    int x1, x2, x3, x4;

    x3 = 0;
    x4 = 0;

    while (x4 < 1) {
        if (x2 < x1) {
            x2 = x1;
        }
        x4 = x4 + 1;
    }

    assert(x1 <= x2);
}