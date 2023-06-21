int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 6;
  int junk_2 = 7;
  int junk_3 = 7;
  int junk_4 = 4;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = junk_4 - (junk_0);
    y = ((y) + (1));
    junk_3 = junk_2;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
