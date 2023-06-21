int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 0;
  int junk_3 = 7;
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
      junk_2 = 453 + (junk_0);
      x = y;
      junk_0 = junk_4;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_1 - (598);
      x = y;
      junk_3 = 462;
      y = ((y) + (1));
      junk_1 = 890;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
