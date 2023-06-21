int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 7;
  int junk_3 = 9;
  int junk_4 = 9;
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
      junk_4 = 932 - (756);
      c = ((c) + (1));
      junk_0 = junk_1;
    }
    else{
      //fb 
    }
  }
    //fb 
  if(((c) < (36))) {
    //tb 
    assert ((z) < (4608));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
