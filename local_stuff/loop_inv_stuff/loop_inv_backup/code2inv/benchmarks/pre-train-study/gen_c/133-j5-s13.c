int main()
{
  int n;
  int x;
  int junk_0 = 3;
  int junk_1 = 1;
  int junk_2 = 8;
  int junk_3 = 9;
  int junk_4 = 1;
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
