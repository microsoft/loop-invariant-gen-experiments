int main()
{
  int i;
  int j;
  int junk_0 = 6;
  int junk_1 = 7;
  int junk_2 = 1;
  //skip 
  i = 1;
  
  j = 10;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_2 = junk_0 - (2);
    j = ((j) - (1));
    junk_2 = junk_2 + (junk_1);
  }
    //fb 
  assert ((j) == (6));
  //skip 


}
