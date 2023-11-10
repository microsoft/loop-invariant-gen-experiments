extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
int f1(int z) {
    int x = 1;
    int y = 0;

    while (x <= 9) { // <--- loop condition: x<=9
        y = x + 2;
        x = 2 * y;
    }

    return 2 * x;
}

int f2(int z) {
    int y = 0;
    int x = 1;

    while (x < 10) { // <--- loop condition: x<10, (only syntactic differences)
        y = 2 + x;
        x = y + y;
    }

    return x * 2;
}

void main()
{
	int z = unknown();
	int res1=f1(z);
	int res2=f2(z);
	assert(res1==res2);
}
