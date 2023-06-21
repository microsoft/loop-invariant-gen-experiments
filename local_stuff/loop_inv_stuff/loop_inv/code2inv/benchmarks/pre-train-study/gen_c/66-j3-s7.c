int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 5;
  int junk_2 = 4;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_0 = 10;
    x = ((x) + (1));
    junk_2 = junk_0;
  }
    //fb 
  assert ((y) < (100));
  //skip 


}
