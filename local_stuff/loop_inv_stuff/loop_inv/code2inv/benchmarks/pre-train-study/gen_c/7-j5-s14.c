int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 3;
  int junk_4 = 0;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_3 = junk_0;
    y = ((y) + (10));
    junk_0 = 375;
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
