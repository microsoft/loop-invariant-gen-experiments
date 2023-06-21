int main()
{
  int n;
  int x;
  int junk_0 = 7;
  int junk_1 = 0;
  int junk_2 = 9;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_1 = junk_0 + (junk_0);
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
