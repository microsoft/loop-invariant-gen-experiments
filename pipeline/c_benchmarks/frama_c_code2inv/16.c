#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);



int main()
{
    int x = 0;
    int m = 0;
    int n;

    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    if(n > 0) {
       //assert (m < n);
       assert (m >= 0);
    }
}
