int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 8;
  int junk_2 = 0;
  int junk_3 = 7;
  int junk_4 = 1;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_3 = junk_2;
    y = ((y) + (1));
    junk_1 = 266 + (junk_3);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
