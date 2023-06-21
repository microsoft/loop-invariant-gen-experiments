int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 9;
  int junk_2 = 7;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_0 = 540;
    y = ((y) + (10));
    junk_0 = junk_1 - (607);
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
