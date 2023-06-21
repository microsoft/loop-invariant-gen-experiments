int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 4;
  int junk_2 = 8;
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
      junk_1 = junk_2 - (334);
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
