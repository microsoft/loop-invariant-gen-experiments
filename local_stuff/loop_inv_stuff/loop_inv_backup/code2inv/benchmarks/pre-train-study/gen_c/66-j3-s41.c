int main()
{
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 6;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_0 = 999;
    x = ((x) + (1));
    junk_1 = 550 + (junk_0);
  }
    //fb 
  assert ((y) < (100));
  //skip 


}
