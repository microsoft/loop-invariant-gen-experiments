int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 8;
  int junk_2 = 4;
  int junk_3 = 0;
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
      junk_4 = junk_3 - (junk_4);
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
