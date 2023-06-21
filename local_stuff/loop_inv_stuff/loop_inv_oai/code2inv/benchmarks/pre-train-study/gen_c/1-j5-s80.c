int main()
{
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 8;
  int junk_4 = 2;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = junk_0;
    y = ((y) + (1));
    junk_1 = junk_0 - (41);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
