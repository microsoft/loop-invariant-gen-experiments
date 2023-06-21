int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 9;
  int junk_2 = 1;
  int junk_3 = 0;
  int junk_4 = 7;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_2 = junk_0;
    x = ((x) - (1));
    junk_2 = 333;
  }
    //fb 
  assert ((y) == (n));
  //skip 


}
