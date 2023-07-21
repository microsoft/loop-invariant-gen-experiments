#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);



int main(){
    int z1,z2,z3;

    int x = 0;
    int y = 0;

    while(y >= 0){
        y = y + x;
    }

    assert( y>= 0);
}
