int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 0;
  int junk_2 = 4;
  int junk_3 = 4;
  int junk_4 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 164;
      x = y;
      junk_1 = 431;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 697;
      x = y;
      junk_1 = junk_0;
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
