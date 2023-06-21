int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 8;
  int junk_2 = 1;
  int junk_3 = 2;
  int junk_4 = 2;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (2));
  assume ((y) <= (2));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (2));
    junk_3 = junk_0 + (junk_1);
    y = ((y) + (2));
    junk_2 = junk_0 + (junk_4);
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
