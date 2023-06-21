int main()
{
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 9;
  int junk_2 = 4;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = 801;
    y = ((y) + (1));
    junk_2 = junk_0 + (junk_0);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
