#include "seahorn/seahorn.h"
extern int unknown();

int main(){

    int x = 0;
    int y = 0;

    while(y >= 0){
        y = y + x;
    }

    sassert( y>= 0);
}
