int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 1;
  int junk_2 = 7;
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
    junk_2 = 336 + (junk_2);
  }
    //fb 
  assert ((n) == (((x) + (y))));
  //skip 


}
