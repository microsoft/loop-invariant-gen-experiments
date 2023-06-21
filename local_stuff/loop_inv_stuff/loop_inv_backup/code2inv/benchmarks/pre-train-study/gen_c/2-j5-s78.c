int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 1;
  int junk_2 = 3;
  int junk_3 = 0;
  int junk_4 = 1;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_1 = 999;
    y = ((y) + (1));
    junk_2 = 650;
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
