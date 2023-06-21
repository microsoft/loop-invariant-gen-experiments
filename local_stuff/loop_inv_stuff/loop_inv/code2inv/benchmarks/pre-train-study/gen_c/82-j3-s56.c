int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 9;
  int junk_2 = 2;
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
      junk_1 = junk_2;
    }
    else{
      //fb 
    }
  }
    //fb 
  if(((i) >= (x))) {
    //tb 
    if(((0) > (i))) {
      //tb 
      assert ((i) >= (y));
    }
    else{
      //fb 
    }
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
