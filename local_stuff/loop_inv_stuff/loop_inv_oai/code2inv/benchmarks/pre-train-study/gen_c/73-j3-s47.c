int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 6;
  int junk_1 = 5;
  int junk_2 = 0;
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
      junk_2 = junk_0 - (12);
      c = ((c) + (1));
      junk_0 = junk_2;
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
