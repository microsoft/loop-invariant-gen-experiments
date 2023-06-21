int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 7;
  int junk_4 = 5;
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
    junk_0 = 941;
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
