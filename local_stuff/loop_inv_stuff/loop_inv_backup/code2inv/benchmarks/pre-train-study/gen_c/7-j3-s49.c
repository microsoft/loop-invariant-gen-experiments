int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 3;
  int junk_2 = 4;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_0 = junk_0;
    y = ((y) + (10));
    junk_1 = junk_1;
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
