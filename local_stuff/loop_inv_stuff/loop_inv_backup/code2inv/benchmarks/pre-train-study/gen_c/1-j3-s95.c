int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 5;
  int junk_2 = 3;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_2 = junk_1;
    y = ((y) + (1));
    junk_2 = junk_2 - (716);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
