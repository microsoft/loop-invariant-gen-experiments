int main()
{
  int n;
  int x;
  int junk_0 = 5;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_0 = junk_0;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
