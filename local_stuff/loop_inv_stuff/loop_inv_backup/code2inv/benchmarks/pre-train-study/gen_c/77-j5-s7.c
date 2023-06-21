int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 8;
  int junk_2 = 6;
  int junk_3 = 1;
  int junk_4 = 6;
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
      junk_3 = junk_3 - (611);
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
