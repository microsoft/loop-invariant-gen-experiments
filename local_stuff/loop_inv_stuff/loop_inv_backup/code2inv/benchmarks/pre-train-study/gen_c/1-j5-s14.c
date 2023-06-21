int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 3;
  int junk_3 = 7;
  int junk_4 = 7;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = junk_2;
    y = ((y) + (1));
    junk_0 = 996;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
