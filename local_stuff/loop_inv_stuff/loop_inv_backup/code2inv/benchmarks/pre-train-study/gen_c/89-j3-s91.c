int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 7;
  int junk_2 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 565;
      x = y;
      junk_2 = 416 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_1 = 938;
      y = ((y) + (1));
      junk_2 = 695 - (154);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
