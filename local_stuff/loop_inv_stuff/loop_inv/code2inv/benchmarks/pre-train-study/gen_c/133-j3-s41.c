int main()
{
  int n;
  int x;
  int junk_0 = 2;
  int junk_1 = 9;
  int junk_2 = 2;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_0 = junk_1;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
