int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 3;
  int junk_3 = 8;
  int junk_4 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_4;
      x = y;
      junk_2 = 925 - (649);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 653 + (junk_3);
      x = y;
      junk_3 = junk_4 + (690);
      y = ((y) + (1));
      junk_2 = junk_1 + (93);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
