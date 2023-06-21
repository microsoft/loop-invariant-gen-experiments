int main()
{
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 8;
  int junk_2 = 9;
  int junk_3 = 8;
  int junk_4 = 8;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_3 = junk_1;
    y = ((y) + (1));
    junk_1 = 856;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
