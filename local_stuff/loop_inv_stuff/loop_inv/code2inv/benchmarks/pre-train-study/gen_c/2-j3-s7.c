int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 3;
  int junk_2 = 2;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = junk_0;
    y = ((y) + (1));
    junk_0 = 735;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
