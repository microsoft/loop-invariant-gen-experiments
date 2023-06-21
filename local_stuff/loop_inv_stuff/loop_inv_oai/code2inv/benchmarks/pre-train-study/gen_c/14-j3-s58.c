int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 4;
  int junk_2 = 7;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_2 = junk_0 - (642);
    y = ((y) + (2));
    junk_1 = 31 + (834);
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
