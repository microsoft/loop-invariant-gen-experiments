int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 0;
  int junk_3 = 1;
  int junk_4 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_4;
      x = y;
      junk_1 = 485 - (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 511;
      x = y;
      junk_2 = junk_1;
      y = ((y) + (1));
      junk_0 = 907 - (697);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
