int main()
{
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 2;
  int junk_3 = 2;
  int junk_4 = 3;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_4 = junk_2;
    y = ((y) + (1));
    junk_4 = junk_4 + (204);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
