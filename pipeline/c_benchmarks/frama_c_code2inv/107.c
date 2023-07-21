#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);



int main() {
    int a,m,j,k;

    j = 0;
    k = 0;

    while ( k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    assert( a <= m);
}
