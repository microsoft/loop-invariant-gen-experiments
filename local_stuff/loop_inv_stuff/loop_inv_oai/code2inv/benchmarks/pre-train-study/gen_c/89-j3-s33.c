int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 3;
  int junk_2 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_1 = junk_1 - (715);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_2;
      x = y;
      junk_0 = junk_1 + (junk_1);
      y = ((y) + (1));
      junk_2 = 102 - (830);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
