int main()
{
  int i;
  int j;
  int junk_0 = 7;
  int junk_1 = 3;
  int junk_2 = 8;
  //skip 
  i = 1;
  
  j = 10;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_1 = junk_0;
    j = ((j) - (1));
    junk_0 = junk_2;
  }
    //fb 
  assert ((j) == (6));
  //skip 


}
