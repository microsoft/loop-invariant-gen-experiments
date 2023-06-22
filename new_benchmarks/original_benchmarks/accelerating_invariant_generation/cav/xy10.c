int nondet(){
  int x;
  return x;
}

int main ()
{
  int x = 0;
  int y = 0;
  int z;

  while (nondet()){
    x += 10;
    y += 1;
  }

  if (x <= z && y >= z + 1)
    goto ERROR;


    return;

  ERROR:;
}
