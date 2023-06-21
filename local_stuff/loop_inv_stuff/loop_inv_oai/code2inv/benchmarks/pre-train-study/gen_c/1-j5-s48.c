int main()
{
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 9;
  int junk_2 = 2;
  int junk_3 = 1;
  int junk_4 = 0;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_4 = junk_0;
    y = ((y) + (1));
    junk_1 = junk_2 - (junk_3);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
