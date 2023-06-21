int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 872;
      x = y;
      junk_0 = 317;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 482;
      x = y;
      junk_0 = 627;
      y = ((y) + (1));
      junk_0 = junk_0 - (933);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
