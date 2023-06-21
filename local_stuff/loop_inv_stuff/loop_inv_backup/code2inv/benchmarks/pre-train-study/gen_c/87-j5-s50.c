int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 6;
  int junk_2 = 3;
  int junk_3 = 0;
  int junk_4 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_0 = 32 - (29);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0;
      x = y;
      junk_3 = junk_0 + (junk_2);
      y = ((y) + (1));
      junk_4 = junk_2 - (64);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
