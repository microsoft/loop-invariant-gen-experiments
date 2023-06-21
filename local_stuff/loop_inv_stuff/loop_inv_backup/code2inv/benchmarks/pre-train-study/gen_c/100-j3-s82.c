int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 7;
  int junk_2 = 0;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_2 = junk_1;
    x = ((x) - (1));
    junk_0 = 446 - (junk_2);
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
