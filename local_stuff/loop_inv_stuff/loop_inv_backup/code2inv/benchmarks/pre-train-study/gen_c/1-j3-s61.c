int main()
{
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 0;
  int junk_2 = 9;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_2 = junk_0;
    y = ((y) + (1));
    junk_2 = junk_2;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
