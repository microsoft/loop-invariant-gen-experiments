int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 7;
  int junk_3 = 9;
  int junk_4 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 286 + (327);
      x = y;
      junk_4 = 274;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 505 + (188);
      x = y;
      junk_4 = junk_3;
      y = ((y) + (1));
      junk_1 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
