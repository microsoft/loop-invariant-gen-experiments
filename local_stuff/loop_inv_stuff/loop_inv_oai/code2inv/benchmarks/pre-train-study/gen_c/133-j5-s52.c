int main()
{
  int n;
  int x;
  int junk_0 = 5;
  int junk_1 = 0;
  int junk_2 = 3;
  int junk_3 = 5;
  int junk_4 = 4;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_2 = junk_2;
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
