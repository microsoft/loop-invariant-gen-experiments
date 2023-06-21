int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 1;
  int junk_2 = 4;
  int junk_3 = 3;
  int junk_4 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 260 - (junk_4);
      x = y;
      junk_1 = junk_3 - (59);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_4;
      x = y;
      junk_1 = junk_4;
      y = ((y) + (1));
      junk_1 = 75;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
