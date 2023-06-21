int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 5;
  int junk_2 = 0;
  int junk_3 = 4;
  int junk_4 = 9;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_1 = 715 + (junk_3);
    y = ((y) + (10));
    junk_0 = 716;
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
