int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_1 - (64);
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 276;
      x = y;
      junk_2 = 633 - (75);
      y = ((y) + (1));
      junk_2 = 342 + (323);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
