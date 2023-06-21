int main()
{
  int n;
  int x;
  int junk_0 = 9;
  int junk_1 = 3;
  int junk_2 = 0;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_1 = junk_2;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
