int main() {
    int x1 = 1;
    int x2;

    while (x1 <= 10) {
        x2 = 10 - x1;
        x1 = x1 + 1;
    }

    //assert (x2 >= 0);
    assert (x2 < 10);
}