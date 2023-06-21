int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 1;
  int junk_2 = 0;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_0 = 267 + (914);
    y = ((y) + (2));
    junk_1 = 418 - (535);
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
