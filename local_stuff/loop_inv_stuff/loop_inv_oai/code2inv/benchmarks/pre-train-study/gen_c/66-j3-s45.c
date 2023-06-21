int main()
{
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 1;
  int junk_2 = 2;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_1 = junk_2;
    x = ((x) + (1));
    junk_2 = 99;
  }
    //fb 
  assert ((y) < (100));
  //skip 


}
