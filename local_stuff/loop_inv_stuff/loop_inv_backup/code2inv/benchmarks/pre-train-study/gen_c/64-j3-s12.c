int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 2;
  int junk_2 = 2;
  //skip 
  x = 1;
  
  while(((x) <= (10)))
  {
    //tb 
    y = ((10) - (x));
    junk_1 = junk_0;
    x = ((x) + (1));
    junk_0 = junk_0;
  }
    //fb 
  assert ((y) < (10));
  //skip 


}
