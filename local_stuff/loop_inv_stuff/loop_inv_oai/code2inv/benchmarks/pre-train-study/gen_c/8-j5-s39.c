int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 5;
  int junk_2 = 8;
  int junk_3 = 7;
  int junk_4 = 8;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_3 = junk_3 - (418);
    y = ((y) + (10));
    junk_3 = 366;
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
