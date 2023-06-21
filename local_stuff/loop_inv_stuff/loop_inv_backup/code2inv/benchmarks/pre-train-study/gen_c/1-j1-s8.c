int main()
{
  int x;
  int y;
  int junk_0 = 1;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = 127;
    y = ((y) + (1));
    junk_0 = 191;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
