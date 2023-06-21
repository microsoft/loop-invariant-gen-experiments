int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 7;
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
    junk_2 = 619 + (junk_2);
    y = ((y) + (2));
    junk_1 = junk_2;
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
