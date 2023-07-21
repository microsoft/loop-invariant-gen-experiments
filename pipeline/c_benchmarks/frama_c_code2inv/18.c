#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);


int main()
{
    int x = 1;
    int m = 1;
    int n;

    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    if(n > 1) {
       //assert (m < n);
       assert (m >= 1);
    }
}
