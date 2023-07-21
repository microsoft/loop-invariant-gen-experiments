#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);


int main() {
    int a,c,m,j,k;

    assume(a <= m);
    j = 0;
    k = 0;

    while ( k < c) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    assert( a <=  m);
}
