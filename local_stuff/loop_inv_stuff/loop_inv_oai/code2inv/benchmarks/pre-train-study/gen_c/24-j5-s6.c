int main()
{
  int i;
  int j;
  int junk_0 = 1;
  int junk_1 = 1;
  int junk_2 = 6;
  int junk_3 = 9;
  int junk_4 = 9;
  //skip 
  i = 1;
  
  j = 10;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_0 = junk_1;
    j = ((j) - (1));
    junk_2 = junk_2;
  }
    //fb 
  assert ((j) == (6));
  //skip 


}
