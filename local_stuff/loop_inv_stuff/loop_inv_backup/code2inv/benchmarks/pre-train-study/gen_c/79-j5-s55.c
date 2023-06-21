int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 7;
  int junk_3 = 5;
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
      junk_1 = 146 - (junk_3);
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
