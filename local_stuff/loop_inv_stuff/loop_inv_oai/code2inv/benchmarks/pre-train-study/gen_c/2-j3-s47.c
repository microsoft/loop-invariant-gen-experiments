int main()
{
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 3;
  int junk_2 = 4;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = junk_1;
    y = ((y) + (1));
    junk_1 = 631;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
