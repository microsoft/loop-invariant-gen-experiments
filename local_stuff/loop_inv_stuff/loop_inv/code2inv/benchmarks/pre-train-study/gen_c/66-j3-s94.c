int main()
{
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 6;
  int junk_2 = 5;
  //skip 
  x = 1;
  
  while(((x) <= (100)))
  {
    //tb 
    y = ((100) - (x));
    junk_1 = junk_2;
    x = ((x) + (1));
    junk_2 = junk_2 - (junk_2);
  }
    //fb 
  assert ((y) < (100));
  //skip 


}
