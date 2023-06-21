int main()
{
  int n;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 1;
  int junk_3 = 1;
  int junk_4 = 5;
  //skip 
  assume ((n) >= (0));
  x = n;
  
  y = 0;
  
  while(((x) > (0)))
  {
    //tb 
    y = ((y) + (1));
    junk_4 = junk_2;
    x = ((x) - (1));
    junk_3 = junk_3 - (junk_0);
  }
    //fb 
  assert ((n) == (((x) + (y))));
  //skip 


}
