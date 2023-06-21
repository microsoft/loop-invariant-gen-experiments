int main()
{
  int c;
  int n;
  int tmp;
  int tmp___0;
  int junk_0 = 0;
  int junk_1 = 1;
  int junk_2 = 0;
  int junk_3 = 2;
  int junk_4 = 9;
  //skip 
  c = 0;
  
  assume ((n) > (0));
  while(unknown())
  {
    //tb 
    if(unknown()) {
      //tb 
      if(((c) != (n))) {
        //tb 
        c = ((c) + (1));
        junk_0 = junk_4;
      }
      else{
        //fb 
      }
    }
    else{
      //fb 
      if(((c) == (n))) {
        //tb 
        c = 1;
        junk_0 = 171;
      }
      else{
        //fb 
      }
    }
  }
    //fb 
  if(((c) != (n))) {
    //tb 
    assert ((c) >= (0));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
