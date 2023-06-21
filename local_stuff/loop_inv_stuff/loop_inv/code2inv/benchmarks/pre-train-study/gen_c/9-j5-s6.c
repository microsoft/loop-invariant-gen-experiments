int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 5;
  int junk_2 = 8;
  int junk_3 = 4;
  int junk_4 = 5;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_1 = junk_4;
    y = ((y) + (2));
    junk_0 = 585;
  }
    //fb 
  if(((x) == (4))) {
    //tb 
    assert ((y) != (0));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
