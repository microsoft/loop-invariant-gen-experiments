int main()
{
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 3;
  int junk_2 = 7;
  int junk_3 = 0;
  int junk_4 = 9;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = junk_1 + (599);
    y = ((y) + (1));
    junk_1 = junk_3;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
