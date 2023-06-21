int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 6;
  int junk_2 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_2;
      x = y;
      junk_1 = 403 - (436);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_1 + (junk_0);
      x = y;
      junk_1 = 380 - (junk_2);
      y = ((y) + (1));
      junk_0 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
