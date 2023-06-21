int main()
{
  int x;
  int junk_0 = 5;
  int junk_1 = 8;
  int junk_2 = 5;
  int junk_3 = 0;
  int junk_4 = 0;
  //skip 
  x = 0;
  
  while(((x) < (100)))
  {
    //tb 
    x = ((x) + (1));
    junk_3 = junk_2;
  }
    //fb 
  assert ((x) == (100));
  //skip 


}
