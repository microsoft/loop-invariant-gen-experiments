int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 8;
  int junk_2 = 9;
  int junk_3 = 5;
  int junk_4 = 8;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_2 = junk_1 + (junk_0);
    x = ((x) - (1));
    junk_4 = junk_2;
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
