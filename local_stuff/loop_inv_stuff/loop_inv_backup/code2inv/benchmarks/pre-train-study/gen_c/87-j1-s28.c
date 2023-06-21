int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 273;
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 785;
      x = y;
      junk_0 = 736 - (junk_0);
      y = ((y) + (1));
      junk_0 = 896;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
