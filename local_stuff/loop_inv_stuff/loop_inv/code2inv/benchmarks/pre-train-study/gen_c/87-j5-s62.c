int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 1;
  int junk_2 = 2;
  int junk_3 = 9;
  int junk_4 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 251;
      x = y;
      junk_1 = 8;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 369 - (780);
      x = y;
      junk_0 = 79;
      y = ((y) + (1));
      junk_2 = 655;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
