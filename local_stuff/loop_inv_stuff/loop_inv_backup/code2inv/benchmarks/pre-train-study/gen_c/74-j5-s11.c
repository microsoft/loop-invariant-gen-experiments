int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 6;
  int junk_3 = 7;
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
      junk_3 = junk_2 + (39);
      c = ((c) + (1));
      junk_2 = junk_3;
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
