int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 276;
      x = y;
      junk_0 = junk_0 + (638);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_0 = 813;
      y = ((y) + (1));
      junk_0 = 999 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
