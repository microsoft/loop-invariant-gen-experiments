int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 3;
  int junk_2 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_1 = junk_0 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 672;
      x = y;
      junk_0 = junk_0 + (541);
      y = ((y) + (1));
      junk_0 = junk_2 - (213);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
