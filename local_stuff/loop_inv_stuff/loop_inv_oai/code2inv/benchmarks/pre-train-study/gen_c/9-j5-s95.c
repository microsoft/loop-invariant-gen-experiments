int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 4;
  int junk_3 = 4;
  int junk_4 = 0;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_3 = junk_0 + (923);
    y = ((y) + (2));
    junk_4 = 132;
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
