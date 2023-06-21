int main()
{
  int i;
  int j;
  int junk_0 = 2;
  int junk_1 = 8;
  int junk_2 = 1;
  int junk_3 = 4;
  int junk_4 = 5;
  //skip 
  i = 1;
  
  j = 10;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_2 = junk_1;
    j = ((j) - (1));
    junk_1 = junk_1;
  }
    //fb 
  assert ((j) == (6));
  //skip 


}
