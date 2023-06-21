int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 9;
  int junk_1 = 6;
  int junk_2 = 7;
  int junk_3 = 5;
  int junk_4 = 6;
  //skip 
  c = 0;
  
  assume ((y) >= (0));
  assume ((y) >= (127));
  z = ((36) * (y));
  
  while(unknown())
  {
    //tb 
    if(((c) < (36))) {
      //tb 
      z = ((z) + (1));
      junk_0 = junk_0;
      c = ((c) + (1));
      junk_2 = 127;
    }
    else{
      //fb 
    }
  }
    //fb 
  if(((z) < (0))) {
    //tb 
    if(((z) >= (4608))) {
      //tb 
      assert ((c) >= (36));
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
