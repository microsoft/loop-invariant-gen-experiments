int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 3;
  int junk_2 = 2;
  int junk_3 = 3;
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
      junk_1 = junk_2 - (junk_0);
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
