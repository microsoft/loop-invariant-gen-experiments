int main()
{
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 9;
  int junk_3 = 7;
  int junk_4 = 9;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (1000)))
  {
    //tb 
    x = ((x) + (y));
    junk_4 = junk_1;
    y = ((y) + (1));
    junk_2 = junk_2 + (junk_4);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
