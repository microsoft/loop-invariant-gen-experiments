int main()
{
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 6;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_2 = junk_0;
    y = ((y) + (1));
    junk_1 = junk_0;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
