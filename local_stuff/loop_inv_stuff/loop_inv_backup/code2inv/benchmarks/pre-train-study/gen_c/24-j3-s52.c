int main()
{
  int i;
  int j;
  int junk_0 = 1;
  int junk_1 = 0;
  int junk_2 = 7;
  //skip 
  i = 1;
  
  j = 10;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_0 = junk_1 + (junk_0);
    j = ((j) - (1));
    junk_1 = junk_0;
  }
    //fb 
  assert ((j) == (6));
  //skip 


}
