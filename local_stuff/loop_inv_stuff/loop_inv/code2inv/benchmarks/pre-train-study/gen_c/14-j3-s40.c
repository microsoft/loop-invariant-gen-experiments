int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 9;
  int junk_2 = 1;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_2 = 123 + (672);
    y = ((y) + (2));
    junk_2 = junk_0 - (714);
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
