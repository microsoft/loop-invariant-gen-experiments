int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
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
      junk_0 = 775;
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
