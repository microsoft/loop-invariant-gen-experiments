int main()
{
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 2;
  int junk_2 = 4;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_2 = 916;
    y = ((y) + (1));
    junk_2 = junk_1;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
