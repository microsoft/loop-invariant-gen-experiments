int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 0;
  int junk_1 = 8;
  int junk_2 = 2;
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
      junk_1 = junk_2 - (670);
      c = ((c) + (1));
      junk_1 = junk_1;
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
