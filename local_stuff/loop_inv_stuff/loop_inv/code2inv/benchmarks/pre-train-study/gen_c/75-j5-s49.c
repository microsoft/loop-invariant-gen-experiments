int main()
{
  int c;
  int tmp;
  int y;
  int z;
  int junk_0 = 2;
  int junk_1 = 5;
  int junk_2 = 0;
  int junk_3 = 3;
  int junk_4 = 1;
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
      junk_3 = junk_0 + (143);
      c = ((c) + (1));
      junk_2 = junk_3 - (614);
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
