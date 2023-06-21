int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
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
      junk_0 = 251;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 8;
      x = y;
      junk_0 = 369 - (780);
      y = ((y) + (1));
      junk_0 = 79;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
