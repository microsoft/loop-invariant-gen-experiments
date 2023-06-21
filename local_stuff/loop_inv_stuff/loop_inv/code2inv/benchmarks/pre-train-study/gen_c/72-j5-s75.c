int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 3;
  int junk_1 = 2;
  int junk_2 = 7;
  int junk_3 = 5;
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
      junk_4 = 380 - (junk_4);
      c = ((c) + (1));
      junk_4 = junk_4 - (junk_4);
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
