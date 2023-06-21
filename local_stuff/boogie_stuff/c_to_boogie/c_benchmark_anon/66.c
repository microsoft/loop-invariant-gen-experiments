int main() {
    int x1 = 1;
    int x2;

    while (x1 <= 100) {
        x2 = 100 - x1;
        x1 = x1 + 1;
    }

    //assert (x2 >= 0);
    assert (x2 < 100);
}