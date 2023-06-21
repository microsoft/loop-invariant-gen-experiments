int main()
{
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 2;
  //skip 
  x = 1;
  
  while(((x) <= (10)))
  {
    //tb 
    y = ((10) - (x));
    junk_0 = junk_2;
    x = ((x) + (1));
    junk_1 = junk_2;
  }
    //fb 
  assert ((y) < (10));
  //skip 


}
