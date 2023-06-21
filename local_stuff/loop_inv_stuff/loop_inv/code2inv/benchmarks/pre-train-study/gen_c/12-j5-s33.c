int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 0;
  int junk_2 = 5;
  int junk_3 = 6;
  int junk_4 = 5;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_2 = 520;
    y = ((y) + (10));
    junk_2 = 836;
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
