int main()
{
  int i;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 1;
  int junk_3 = 4;
  int junk_4 = 8;
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
      junk_2 = junk_3 + (junk_0);
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
