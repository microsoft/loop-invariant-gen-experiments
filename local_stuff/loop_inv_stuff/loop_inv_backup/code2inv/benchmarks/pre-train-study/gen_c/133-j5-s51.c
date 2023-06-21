int main()
{
  int n;
  int x;
  int junk_0 = 3;
  int junk_1 = 4;
  int junk_2 = 1;
  int junk_3 = 4;
  int junk_4 = 9;
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
