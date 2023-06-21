int main()
{
  int n;
  int x;
  int junk_0 = 8;
  int junk_1 = 2;
  int junk_2 = 4;
  int junk_3 = 3;
  int junk_4 = 2;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_1;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
