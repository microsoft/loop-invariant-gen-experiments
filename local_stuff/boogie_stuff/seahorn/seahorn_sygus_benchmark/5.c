#include "seahorn/seahorn.h"
extern int unknown();
int main()
{
    int x = 0;
int size = unknown();
int y = unknown();
int z = unknown();

    while(x < size) {
       x += 1;
       if( z <= y) {
          y = z;
       }
    }

    if(size > 0) {
       sassert (z >= y);
    }
}
