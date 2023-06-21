int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
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
      junk_0 = 286;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 380;
      x = y;
      junk_0 = 423 + (713);
      y = ((y) + (1));
      junk_0 = 624;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
