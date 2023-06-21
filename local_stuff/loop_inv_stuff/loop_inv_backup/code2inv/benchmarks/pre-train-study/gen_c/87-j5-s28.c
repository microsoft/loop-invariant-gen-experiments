int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 8;
  int junk_2 = 6;
  int junk_3 = 7;
  int junk_4 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_2;
      x = y;
      junk_0 = 785;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 736 - (junk_3);
      x = y;
      junk_3 = 896;
      y = ((y) + (1));
      junk_2 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
