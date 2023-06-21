int main()
{
  int i;
  int j;
  int junk_0 = 6;
  int junk_1 = 0;
  int junk_2 = 6;
  int junk_3 = 9;
  int junk_4 = 8;
  //skip 
  i = 1;
  
  j = 20;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_2 = junk_1;
    j = ((j) - (1));
    junk_4 = junk_3;
  }
    //fb 
  assert ((j) == (13));
  //skip 


}
