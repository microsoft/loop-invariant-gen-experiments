int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 4;
  int junk_3 = 7;
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
      junk_1 = 162 + (632);
      x = y;
      junk_0 = junk_4;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 668 - (junk_2);
      x = y;
      junk_2 = junk_0 - (671);
      y = ((y) + (1));
      junk_3 = junk_0 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
