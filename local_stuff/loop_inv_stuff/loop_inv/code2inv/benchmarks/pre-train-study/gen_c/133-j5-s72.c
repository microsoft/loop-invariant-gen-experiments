int main()
{
  int n;
  int x;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 9;
  int junk_3 = 3;
  int junk_4 = 1;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_0 = junk_4;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
