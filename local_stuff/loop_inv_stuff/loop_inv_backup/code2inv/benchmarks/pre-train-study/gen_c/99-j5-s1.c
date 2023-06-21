int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 2;
  int junk_2 = 0;
  int junk_3 = 2;
  int junk_4 = 0;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_0 = junk_3 + (64);
    x = ((x) - (1));
    junk_1 = junk_2;
  }
    //fb 
  assert ((n) == (((x) + (y))));
  //skip 


}
