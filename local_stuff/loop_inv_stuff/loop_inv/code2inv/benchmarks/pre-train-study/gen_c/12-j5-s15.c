int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 0;
  int junk_2 = 4;
  int junk_3 = 9;
  int junk_4 = 3;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_2 = junk_1;
    y = ((y) + (10));
    junk_1 = 647;
  }
    //fb 
  if(((y) == (0))) {
    //tb 
    assert ((x) != (20));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
