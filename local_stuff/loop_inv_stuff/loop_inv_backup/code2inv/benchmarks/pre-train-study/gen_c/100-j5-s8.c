int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 9;
  int junk_2 = 6;
  int junk_3 = 1;
  int junk_4 = 9;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_4 = junk_3;
    x = ((x) - (1));
    junk_3 = junk_2;
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
