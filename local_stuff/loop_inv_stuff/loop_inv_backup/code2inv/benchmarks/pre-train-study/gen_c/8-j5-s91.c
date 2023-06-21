int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 8;
  int junk_2 = 1;
  int junk_3 = 6;
  int junk_4 = 0;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_4 = junk_4;
    y = ((y) + (10));
    junk_3 = 180;
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
