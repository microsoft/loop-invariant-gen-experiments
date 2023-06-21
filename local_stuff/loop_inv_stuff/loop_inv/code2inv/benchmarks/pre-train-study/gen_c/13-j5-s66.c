int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 8;
  int junk_2 = 4;
  int junk_3 = 7;
  int junk_4 = 2;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_3 = 451;
    y = ((y) + (2));
    junk_0 = 708;
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
