int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 3;
  int junk_2 = 0;
  int junk_3 = 3;
  int junk_4 = 3;
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
      junk_1 = 595;
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
