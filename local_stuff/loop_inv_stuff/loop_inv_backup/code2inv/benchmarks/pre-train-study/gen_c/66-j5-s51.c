int main()
{
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 0;
  int junk_2 = 1;
  int junk_3 = 0;
  int junk_4 = 4;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_0 = junk_2;
    x = ((x) + (1));
    junk_0 = junk_0;
  }
    //fb 
  assert ((y) < (100));
  //skip 


}
