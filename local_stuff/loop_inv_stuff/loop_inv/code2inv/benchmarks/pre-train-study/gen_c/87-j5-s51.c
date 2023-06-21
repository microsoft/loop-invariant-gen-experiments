int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 3;
  int junk_2 = 1;
  int junk_3 = 9;
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
      junk_3 = 83;
      x = y;
      junk_1 = 516;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 32 + (139);
      x = y;
      junk_4 = junk_1 + (590);
      y = ((y) + (1));
      junk_1 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
