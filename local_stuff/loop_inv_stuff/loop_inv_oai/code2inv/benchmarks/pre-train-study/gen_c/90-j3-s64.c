int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0;
      x = y;
      junk_0 = 750;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 999 - (133);
      x = y;
      junk_1 = 719 - (177);
      y = ((y) + (1));
      junk_1 = 728;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
