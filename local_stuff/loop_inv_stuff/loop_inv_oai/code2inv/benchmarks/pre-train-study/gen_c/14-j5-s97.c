int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 1;
  int junk_2 = 2;
  int junk_3 = 7;
  int junk_4 = 7;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_2 = 474;
    y = ((y) + (2));
    junk_4 = 827 + (junk_0);
  }
    //fb 
  if(((y) == (0))) {
    //tb 
    assert ((x) != (4));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
