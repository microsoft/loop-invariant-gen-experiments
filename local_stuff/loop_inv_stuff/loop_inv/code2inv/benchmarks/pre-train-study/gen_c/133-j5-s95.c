int main()
{
  int n;
  int x;
  int junk_0 = 3;
  int junk_1 = 2;
  int junk_2 = 0;
  int junk_3 = 6;
  int junk_4 = 4;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_3 = junk_4;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
