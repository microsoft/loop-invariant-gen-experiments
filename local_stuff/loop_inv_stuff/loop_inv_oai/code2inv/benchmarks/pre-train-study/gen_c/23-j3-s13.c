int main()
{
  int i;
  int j;
  int junk_0 = 7;
  int junk_1 = 8;
  int junk_2 = 9;
  //skip 
  i = 1;
  
  j = 20;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_1 = junk_2;
    j = ((j) - (1));
    junk_2 = junk_1;
  }
    //fb 
  assert ((j) == (13));
  //skip 


}
