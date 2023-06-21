int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 8;
  int junk_2 = 3;
  int junk_3 = 9;
  int junk_4 = 4;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_2 = junk_3 - (junk_1);
    x = ((x) - (1));
    junk_4 = junk_3 + (junk_3);
  }
    //fb 
  assert ((n) == (((x) + (y))));
  //skip 


}
