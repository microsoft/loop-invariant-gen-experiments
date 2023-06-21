int nondet();

int main(){

  int x, y, z;
  x = 0; y = 0; z = 0;

  while (nondet())

  {
    
    x++;
    y++;
    z-=2;
  }
    while (x > 0){
      z++;z++;
      x--;y--;
    }

    if (z <= -1)
      goto ERROR;
  return;
ERROR:;
}
