int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 9;
  int junk_2 = 1;
  int junk_3 = 2;
  int junk_4 = 7;
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
      junk_1 = 740;
    }
    else{
      //fb 
    }
  }
    //fb 
  if(((i) < (y))) {
    //tb 
    assert ((0) <= (i));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
