int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 7;
  int junk_3 = 7;
  int junk_4 = 1;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_3 = 931 + (junk_0);
    y = ((y) + (10));
    junk_3 = 518;
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
