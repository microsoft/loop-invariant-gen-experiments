int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 6;
  int junk_3 = 2;
  int junk_4 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 541;
      x = y;
      junk_4 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 283;
      x = y;
      junk_0 = 260;
      y = ((y) + (1));
      junk_1 = 402 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
