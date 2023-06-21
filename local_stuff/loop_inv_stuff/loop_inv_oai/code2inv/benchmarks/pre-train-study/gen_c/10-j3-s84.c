int main()
{
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
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
    junk_2 = 961;
    y = ((y) + (2));
    junk_1 = 710 + (694);
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
