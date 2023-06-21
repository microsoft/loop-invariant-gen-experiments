int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 6;
  int junk_2 = 3;
  int junk_3 = 3;
  int junk_4 = 1;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_0 = 911 + (junk_2);
    y = ((y) + (2));
    junk_3 = junk_3 - (85);
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
