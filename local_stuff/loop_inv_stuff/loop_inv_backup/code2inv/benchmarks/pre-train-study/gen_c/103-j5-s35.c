int main()
{
  int x;
  int junk_0 = 7;
  int junk_1 = 1;
  int junk_2 = 6;
  int junk_3 = 2;
  int junk_4 = 1;
  //skip 
  x = 0;
  
  while(((x) < (100)))
  {
    //tb 
    x = ((x) + (1));
    junk_4 = junk_3;
  }
    //fb 
  assert ((x) == (100));
  //skip 


}
