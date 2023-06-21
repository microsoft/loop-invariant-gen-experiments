int main()
{
  int c;
  int n;
  int tmp;
  int tmp___0;
  int junk_0 = 9;
  int junk_1 = 3;
  int junk_2 = 0;
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
        junk_1 = 276;
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
        junk_0 = junk_2 + (152);
      }
      else{
        //fb 
      }
    }
  }
    //fb 
  if(((c) != (n))) {
    //tb 
    assert ((c) <= (n));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
