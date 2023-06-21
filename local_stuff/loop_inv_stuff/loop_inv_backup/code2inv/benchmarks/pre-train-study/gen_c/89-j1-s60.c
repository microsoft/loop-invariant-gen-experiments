int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0;
      x = y;
      junk_0 = 27;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 116 - (junk_0);
      x = y;
      junk_0 = 940;
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
