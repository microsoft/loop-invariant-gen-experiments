int main()
{
  int c;
  int n;
  int tmp;
  int tmp___0;
  int junk_0 = 8;
  int junk_1 = 4;
  int junk_2 = 4;
  int junk_3 = 3;
  int junk_4 = 3;
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
        junk_1 = junk_0;
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
        junk_4 = junk_2;
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
