int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 4;
  int junk_2 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 338;
      x = y;
      junk_2 = 240;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 438 + (junk_0);
      x = y;
      junk_2 = 685 + (junk_2);
      y = ((y) + (1));
      junk_1 = 559 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
