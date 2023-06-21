int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 7;
  int junk_2 = 1;
  //skip 
  i = 0;
  
  assume ((x) >= (0));
  assume ((y) >= (0));
  assume ((x) >= (y));
  while(unknown())
  {
    //tb 
    if(((i) < (y))) {
      //tb 
      i = ((i) + (1));
      junk_0 = 959;
    }
    else{
      //fb 
    }
  }
    //fb 
  if(((i) < (y))) {
    //tb 
    assert ((i) < (x));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
