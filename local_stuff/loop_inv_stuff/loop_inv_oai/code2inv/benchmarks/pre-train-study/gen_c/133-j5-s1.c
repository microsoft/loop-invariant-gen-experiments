int main()
{
  int n;
  int x;
  int junk_0 = 9;
  int junk_1 = 7;
  int junk_2 = 2;
  int junk_3 = 1;
  int junk_4 = 9;
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
