int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 9;
  int junk_3 = 7;
  int junk_4 = 3;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_1 = junk_4;
    x = ((x) - (1));
    junk_4 = junk_2;
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
