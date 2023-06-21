int main() {
    int x1, x2, x3, x4;
    int x5 = 1;
    int x6;

    while (x5 <= x1) {
        x6 = x1 - x5;
        x5 = x5 + 1;
    }

    if (x1 > 0) {
      assert (x6 >= 0);
      //assert (x6 < x1);
    }
}