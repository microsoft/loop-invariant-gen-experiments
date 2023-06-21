int main()
{
  int x;
  int junk_0 = 0;
  int junk_1 = 8;
  int junk_2 = 6;
  int junk_3 = 9;
  int junk_4 = 6;
  //skip 
  x = 0;
  
  while(((x) < (100)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_3;
  }
    //fb 
  assert ((x) == (100));
  //skip 


}
