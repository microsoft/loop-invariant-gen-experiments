int main()
{
  int x;
  int junk_0 = 5;
  int junk_1 = 7;
  int junk_2 = 6;
  //skip 
  x = 0;
  
  while(((x) < (100)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_1;
  }
    //fb 
  assert ((x) == (100));
  //skip 


}
