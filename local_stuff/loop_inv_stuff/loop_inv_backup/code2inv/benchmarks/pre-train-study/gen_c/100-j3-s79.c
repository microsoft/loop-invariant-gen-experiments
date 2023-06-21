int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 1;
  int junk_2 = 6;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_1 = junk_1 + (junk_2);
    x = ((x) - (1));
    junk_1 = junk_2 - (junk_2);
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
