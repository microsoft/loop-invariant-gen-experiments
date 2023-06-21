int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 0;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_0 = junk_2;
    x = ((x) - (1));
    junk_0 = 14;
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
