int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 6;
  int junk_2 = 8;
  int junk_3 = 3;
  int junk_4 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 645 - (927);
      x = y;
      junk_2 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 562;
      x = y;
      junk_4 = 166;
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
