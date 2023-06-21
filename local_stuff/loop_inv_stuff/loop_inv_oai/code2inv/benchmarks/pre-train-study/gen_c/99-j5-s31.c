int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 6;
  int junk_2 = 2;
  int junk_3 = 6;
  int junk_4 = 7;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_3 = junk_4 - (junk_3);
    x = ((x) - (1));
    junk_0 = junk_4;
  }
    //fb 
  assert ((n) == (((x) + (y))));
  //skip 


}
