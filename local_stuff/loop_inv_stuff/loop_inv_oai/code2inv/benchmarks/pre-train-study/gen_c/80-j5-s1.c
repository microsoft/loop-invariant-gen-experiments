int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 5;
  int junk_3 = 1;
  int junk_4 = 2;
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
      junk_1 = junk_2 - (junk_4);
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
