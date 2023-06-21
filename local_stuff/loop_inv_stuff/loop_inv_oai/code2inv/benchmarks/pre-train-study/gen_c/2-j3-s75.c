int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 3;
  int junk_2 = 6;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = 850;
    y = ((y) + (1));
    junk_1 = junk_2;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
