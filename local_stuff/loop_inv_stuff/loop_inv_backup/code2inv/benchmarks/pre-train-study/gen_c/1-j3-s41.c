int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 5;
  int junk_2 = 0;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_2 = 212;
    y = ((y) + (1));
    junk_1 = junk_2;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
