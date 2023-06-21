int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 9;
  int junk_2 = 4;
  int junk_3 = 9;
  int junk_4 = 0;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_4 = 417 - (junk_0);
    y = ((y) + (2));
    junk_2 = junk_2 + (450);
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
