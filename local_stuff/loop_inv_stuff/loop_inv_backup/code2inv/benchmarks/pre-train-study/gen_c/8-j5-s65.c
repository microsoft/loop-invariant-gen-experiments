int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 7;
  int junk_2 = 2;
  int junk_3 = 3;
  int junk_4 = 2;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_2 = 552;
    y = ((y) + (10));
    junk_4 = 375;
  }
    //fb 
  if(((y) == (0))) {
    //tb 
    assert ((x) != (20));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
