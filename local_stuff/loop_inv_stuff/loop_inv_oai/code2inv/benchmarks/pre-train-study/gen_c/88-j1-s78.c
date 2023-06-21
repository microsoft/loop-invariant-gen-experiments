int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0;
      x = y;
      junk_0 = 93;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 966;
      x = y;
      junk_0 = 826;
      y = ((y) + (1));
      junk_0 = 808 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
