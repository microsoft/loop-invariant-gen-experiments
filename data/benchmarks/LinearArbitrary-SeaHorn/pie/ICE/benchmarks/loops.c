#include "seahorn/seahorn.h"

int main(int argc, char* argv[])
{
  int x = unknown ();
  if (x >= 0) {

  int y = unknown ();

  int s = 0;
  while (s < x) {
    s++;
  }
  
  y = 0;
  while (y < s) {
    y++;
  }

  sassert(x == y);
  }
}
