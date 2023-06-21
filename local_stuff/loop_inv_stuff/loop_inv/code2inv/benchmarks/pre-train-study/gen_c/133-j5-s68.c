int main()
{
  int n;
  int x;
  int junk_0 = 5;
  int junk_1 = 3;
  int junk_2 = 9;
  int junk_3 = 9;
  int junk_4 = 3;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_1 = junk_3;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
