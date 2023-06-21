int main()
{
  int i;
  int j;
  int junk_0 = 2;
  int junk_1 = 3;
  int junk_2 = 4;
  int junk_3 = 4;
  int junk_4 = 3;
  //skip 
  i = 1;
  
  j = 20;
  
  while(((j) >= (i)))
  {
    //tb 
    i = ((i) + (2));
    junk_3 = junk_4 + (junk_0);
    j = ((j) - (1));
    junk_0 = junk_2;
  }
    //fb 
  assert ((j) == (13));
  //skip 


}
