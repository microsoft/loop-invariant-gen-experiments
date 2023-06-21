int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 8;
  int junk_3 = 0;
  int junk_4 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_0;
      x = y;
      junk_3 = 796 + (junk_4);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 594;
      x = y;
      junk_1 = 717;
      y = ((y) + (1));
      junk_0 = junk_2 - (junk_3);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
