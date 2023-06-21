int main()
{
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 9;
  int junk_2 = 7;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = 63;
    y = ((y) + (1));
    junk_2 = junk_0;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
