int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 3;
  int junk_2 = 4;
  int junk_3 = 3;
  int junk_4 = 0;
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
      junk_0 = 111;
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
