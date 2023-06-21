int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 8;
  int junk_1 = 1;
  int junk_2 = 2;
  int junk_3 = 9;
  int junk_4 = 8;
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
      junk_4 = 501;
      c = ((c) + (1));
      junk_0 = junk_4 + (662);
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
