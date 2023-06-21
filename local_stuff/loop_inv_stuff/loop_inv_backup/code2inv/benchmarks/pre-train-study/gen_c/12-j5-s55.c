int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 9;
  int junk_3 = 3;
  int junk_4 = 5;
  //skip 
  assume ((x) >= (0));
  assume ((x) <= (10));
  assume ((y) <= (10));
  assume ((y) >= (0));
  while(unknown())
  {
    //tb 
    x = ((x) + (10));
    junk_0 = 615;
    y = ((y) + (10));
    junk_4 = 620 + (junk_0);
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
