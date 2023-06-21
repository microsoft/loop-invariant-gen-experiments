int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 7;
  int junk_2 = 3;
  int junk_3 = 5;
  int junk_4 = 6;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_4 = junk_1;
    x = ((x) - (1));
    junk_4 = junk_4 - (junk_0);
  }
    //fb 
  assert ((n) == (((x) + (y))));
  //skip 


}
