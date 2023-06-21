int main()
{
  int n;
  int x;
  int junk_0 = 6;
  int junk_1 = 9;
  int junk_2 = 6;
  int junk_3 = 2;
  int junk_4 = 5;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_3 = junk_2;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
