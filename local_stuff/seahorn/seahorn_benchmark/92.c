#include "seahorn/seahorn.h"
extern int unknown();


int main(){
int z1 = unknown();
int z2 = unknown();
int z3 = unknown();

    int x = 0;
    int y = 0;

    while(y >= 0){
        y = y + x;
    }

    sassert( y>= 0);
}
