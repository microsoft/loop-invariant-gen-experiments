int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 0;
  int junk_3 = 3;
  int junk_4 = 2;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_4 = 489 - (junk_2);
    y = ((y) + (10));
    junk_4 = 947;
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
