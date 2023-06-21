int main()
{
  int i;
  int j;
  int junk_0 = 1;
  int junk_1 = 1;
  int junk_2 = 1;
  int junk_3 = 4;
  int junk_4 = 9;
  //skip 
  i = 1;
  
  j = 20;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_4 = junk_3 + (junk_4);
    j = ((j) - (1));
    junk_4 = junk_3;
  }
    //fb 
  assert ((j) == (13));
  //skip 


}
