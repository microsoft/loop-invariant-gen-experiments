int main()
{
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 6;
  int junk_2 = 0;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = 179;
    y = ((y) + (1));
    junk_0 = 131;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
