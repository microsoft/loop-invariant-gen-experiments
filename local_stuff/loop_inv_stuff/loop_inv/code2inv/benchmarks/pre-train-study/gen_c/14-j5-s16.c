int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 1;
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
    junk_4 = 58;
    y = ((y) + (2));
    junk_3 = 323 + (junk_4);
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
