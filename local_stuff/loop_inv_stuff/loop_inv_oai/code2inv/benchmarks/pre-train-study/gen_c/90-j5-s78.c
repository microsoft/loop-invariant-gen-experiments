int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 7;
  int junk_2 = 2;
  int junk_3 = 9;
  int junk_4 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 93;
      x = y;
      junk_1 = 966;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 826;
      x = y;
      junk_4 = 808 - (junk_4);
      y = ((y) + (1));
      junk_0 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
