int main()
{
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 6;
  int junk_2 = 6;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = junk_2;
    y = ((y) + (1));
    junk_2 = 504;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
