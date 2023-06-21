int main()
{
  int n;
  int x;
  int junk_0 = 8;
  int junk_1 = 4;
  int junk_2 = 3;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_1 = junk_1;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
