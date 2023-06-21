int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 8;
  int junk_2 = 7;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = 26;
    y = ((y) + (1));
    junk_0 = junk_1;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
