int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 6;
  int junk_2 = 6;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_2 = junk_2 + (junk_2);
    y = ((y) + (10));
    junk_1 = 100;
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
