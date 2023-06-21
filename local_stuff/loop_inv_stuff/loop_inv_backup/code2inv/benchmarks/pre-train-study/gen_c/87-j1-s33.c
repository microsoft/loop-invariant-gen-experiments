int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
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
      junk_0 = 407;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 - (830);
      x = y;
      junk_0 = junk_0 - (936);
      y = ((y) + (1));
      junk_0 = junk_0 + (951);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
