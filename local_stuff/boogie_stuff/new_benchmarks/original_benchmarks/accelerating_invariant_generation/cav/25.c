
int unknown1(){
    int x; return x;
}

int unknown2(){
    int x; return x;
}

int unknown3();
int unknown4();

void main()
{
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  while(unknown1())
  {
    while(unknown2())
    {
       if(x==y)
          i++;
       else
          j++;
    }
    if(i>=j)
    {
       x++;
       y++;
    }
    else
       y++;
  }
  if(i <= j-1)
  {goto ERROR; ERROR:;}
}
