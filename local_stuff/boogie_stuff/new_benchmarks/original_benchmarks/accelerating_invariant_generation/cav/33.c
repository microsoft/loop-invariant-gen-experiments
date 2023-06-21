int unknown1(){
    int x; return x;
}

int unknown2(){
    int x; return x;
}

int unknown3(){
    int x; return x;
}


int main()
{
  int k;
  int z = k;
  int x = 0;
  int y = 0;

  while(unknown1())
  {
    int c = 0;
    while(unknown2())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }
    while(unknown3())
    {
      x--;
      y--;
    }
    z=k+y;
  }
  if(x <= y - 1 || x >= y + 1)
  {goto ERROR; ERROR:;}

}
