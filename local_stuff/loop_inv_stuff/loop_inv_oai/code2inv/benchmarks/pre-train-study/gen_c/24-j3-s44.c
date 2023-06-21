int main()
{
  int i;
  int j;
  int junk_0 = 0;
  int junk_1 = 9;
  int junk_2 = 9;
  //skip 
  i = 1;
  
  j = 10;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_2 = junk_1 - (junk_2);
    j = ((j) - (1));
    junk_1 = junk_0;
  }
    //fb 
  assert ((j) == (6));
  //skip 


}
