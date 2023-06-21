int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 6;
  int junk_2 = 4;
  int junk_3 = 4;
  int junk_4 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 713;
      x = y;
      junk_4 = 314;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 769 - (junk_3);
      x = y;
      junk_4 = junk_2 - (970);
      y = ((y) + (1));
      junk_2 = 836;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
