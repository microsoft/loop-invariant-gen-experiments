int main()
{
  int n;
  int x;
  int junk_0 = 1;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 0;
  int junk_4 = 1;
  //skip 
  x = 0;
  
  assume ((n) >= (0));
  while(((x) < (n)))
  {
    //tb 
    x = ((x) + (1));
    junk_3 = junk_2 + (junk_0);
  }
    //fb 
  assert ((x) == (n));
  //skip 


}
