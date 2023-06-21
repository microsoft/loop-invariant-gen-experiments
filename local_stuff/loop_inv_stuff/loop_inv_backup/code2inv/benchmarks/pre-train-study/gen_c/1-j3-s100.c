int main()
{
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 7;
  int junk_2 = 9;
  //skip 
  x = 1;
  
  y = 0;
  
  while(((y) < (100000)))
  {
    //tb 
    x = ((x) + (y));
    junk_0 = junk_1 - (junk_0);
    y = ((y) + (1));
    junk_0 = 164 - (junk_1);
  }
    //fb 
  assert ((x) >= (y));
  //skip 


}
