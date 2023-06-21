int main()
{
  int x;
  int junk_0 = 3;
  int junk_1 = 5;
  int junk_2 = 5;
  //skip 
  x = 0;
  
  while(((x) < (100)))
  {
    //tb 
    x = ((x) + (1));
    junk_1 = junk_2;
  }
    //fb 
  assert ((x) == (100));
  //skip 


}
