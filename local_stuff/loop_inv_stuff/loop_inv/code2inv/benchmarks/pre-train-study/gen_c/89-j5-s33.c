int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 7;
  int junk_2 = 0;
  int junk_3 = 3;
  int junk_4 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = 407;
      x = y;
      junk_3 = junk_1 - (830);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_0 - (936);
      x = y;
      junk_0 = junk_4 + (951);
      y = ((y) + (1));
      junk_3 = 170;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
