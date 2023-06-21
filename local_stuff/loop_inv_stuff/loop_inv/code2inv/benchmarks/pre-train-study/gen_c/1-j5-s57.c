int main()
{
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 8;
  int junk_2 = 4;
  int junk_3 = 7;
  int junk_4 = 5;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = junk_4 - (junk_3);
    y = ((y) + (1));
    junk_4 = junk_0;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
