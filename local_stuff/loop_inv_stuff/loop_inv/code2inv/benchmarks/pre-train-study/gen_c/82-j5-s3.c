int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 4;
  int junk_2 = 4;
  int junk_3 = 3;
  int junk_4 = 5;
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
      junk_3 = 498;
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
