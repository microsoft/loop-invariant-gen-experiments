int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 141;
      x = y;
      junk_0 = 453 + (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_0 = junk_0 - (598);
      y = ((y) + (1));
      junk_0 = 462;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
