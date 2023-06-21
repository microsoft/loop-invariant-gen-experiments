int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 4;
  int junk_2 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 724;
      x = y;
      junk_0 = 244 + (563);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2;
      x = y;
      junk_1 = 477 - (407);
      y = ((y) + (1));
      junk_0 = 390;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
