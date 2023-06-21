int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 5;
  int junk_2 = 5;
  int junk_3 = 4;
  int junk_4 = 6;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_2 = 122;
    y = ((y) + (10));
    junk_3 = junk_4;
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
