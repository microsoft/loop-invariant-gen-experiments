int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 2;
  int junk_2 = 3;
  int junk_3 = 4;
  int junk_4 = 7;
  //skip 
  x = 1;
  
  while(((x) <= (10)))
  {
    //tb 
    y = ((10) - (x));
    junk_1 = junk_0;
    x = ((x) + (1));
    junk_1 = junk_1 + (junk_1);
  }
    //fb 
  assert ((y) < (10));
  //skip 


}
