int main()
{
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 3;
  int junk_2 = 5;
  int junk_3 = 9;
  int junk_4 = 4;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_0 = junk_4;
    x = ((x) + (1));
    junk_4 = junk_0 - (junk_1);
  }
    //fb 
  assert ((y) < (100));
  //skip 


}
