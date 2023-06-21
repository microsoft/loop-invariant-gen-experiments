int main()
{
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 3;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_2 = junk_0;
    x = ((x) + (1));
    junk_2 = junk_0;
  }
    //fb 
  assert ((y) >= (0));
  //skip 


}
