int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 2;
  int junk_2 = 6;
  int junk_3 = 6;
  int junk_4 = 9;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_1 = 467 - (588);
    y = ((y) + (2));
    junk_3 = junk_3 - (junk_4);
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
