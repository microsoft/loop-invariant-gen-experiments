int main()
{
  int x;
  int junk_0 = 1;
  int junk_1 = 5;
  int junk_2 = 2;
  int junk_3 = 1;
  int junk_4 = 5;
  //skip 
  x = 0;
  
  while(((x) < (100)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_4;
  }
    //fb 
  assert ((x) == (100));
  //skip 


}
