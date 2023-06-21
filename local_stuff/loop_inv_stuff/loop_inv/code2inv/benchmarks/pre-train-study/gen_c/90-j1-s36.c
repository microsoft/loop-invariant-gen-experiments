int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 677 + (junk_0);
      x = y;
      junk_0 = 480;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_0 = junk_0 - (181);
      y = ((y) + (1));
      junk_0 = 934;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
