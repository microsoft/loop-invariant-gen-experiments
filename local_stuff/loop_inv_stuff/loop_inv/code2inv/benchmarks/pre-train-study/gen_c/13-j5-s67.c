int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 6;
  int junk_2 = 8;
  int junk_3 = 1;
  int junk_4 = 3;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_4 = junk_4;
    y = ((y) + (2));
    junk_3 = junk_4;
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
