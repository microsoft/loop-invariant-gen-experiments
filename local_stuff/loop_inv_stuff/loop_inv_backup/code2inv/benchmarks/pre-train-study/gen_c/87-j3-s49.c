int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 2;
  int junk_2 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_2;
      x = y;
      junk_2 = 451;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 950 - (519);
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_0 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
