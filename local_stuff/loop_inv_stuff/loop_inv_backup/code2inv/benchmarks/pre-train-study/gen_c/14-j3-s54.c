int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 6;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_1 = 635 + (junk_0);
    y = ((y) + (2));
    junk_1 = 749;
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
