int main()
{
  int n;
  int x;
  int junk_0 = 6;
  int junk_1 = 2;
  int junk_2 = 6;
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
