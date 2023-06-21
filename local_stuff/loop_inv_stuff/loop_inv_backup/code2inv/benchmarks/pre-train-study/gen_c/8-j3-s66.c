int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 6;
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
    junk_0 = junk_0 + (609);
    y = ((y) + (10));
    junk_1 = 675 - (junk_0);
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
