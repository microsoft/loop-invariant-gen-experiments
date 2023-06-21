int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 0;
  int junk_3 = 1;
  int junk_4 = 7;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_1 = junk_0 + (junk_2);
    y = ((y) + (2));
    junk_3 = 462;
  }
    //fb 
  if(((y) == (0))) {
    //tb 
    assert ((x) != (4));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
