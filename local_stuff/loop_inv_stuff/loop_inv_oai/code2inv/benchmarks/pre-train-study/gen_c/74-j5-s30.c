int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 5;
  int junk_3 = 9;
  int junk_4 = 2;
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
      junk_0 = junk_0 - (160);
      c = ((c) + (1));
      junk_4 = junk_0;
    }
    else{
      //fb 
    }
  }
    //fb 
  if(((c) < (36))) {
    //tb 
    assert ((z) >= (0));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
