int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 9;
  int junk_3 = 3;
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
    junk_0 = 25;
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
