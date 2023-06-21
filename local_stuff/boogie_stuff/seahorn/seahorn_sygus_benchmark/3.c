#include "seahorn/seahorn.h"
extern int unknown();

int main()
{
    int x = 0;
int y = unknown();
int z = unknown();

    while(x < 5) {
       x += 1;
       if( z <= y) {
          y = z;
       }
    }

    sassert (z >= y);
}
