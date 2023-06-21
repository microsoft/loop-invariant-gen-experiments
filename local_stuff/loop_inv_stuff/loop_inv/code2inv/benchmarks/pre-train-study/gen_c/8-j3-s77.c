int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 0;
  int junk_2 = 6;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_1 = 830;
    y = ((y) + (10));
    junk_1 = 218;
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
