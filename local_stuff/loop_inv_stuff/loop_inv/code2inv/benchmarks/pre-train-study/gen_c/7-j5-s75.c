int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 0;
  int junk_2 = 4;
  int junk_3 = 1;
  int junk_4 = 4;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_0 = 646;
    y = ((y) + (10));
    junk_1 = junk_4;
  }
    //fb 
  if(((x) == (20))) {
    //tb 
    assert ((y) != (0));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
