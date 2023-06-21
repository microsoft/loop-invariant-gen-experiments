int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 9;
  int junk_1 = 4;
  int junk_2 = 2;
  int junk_3 = 3;
  int junk_4 = 5;
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
      junk_3 = junk_4;
      c = ((c) + (1));
      junk_2 = junk_0;
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
