int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 6;
  int junk_2 = 4;
  int junk_3 = 6;
  int junk_4 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_4 - (116);
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 222 + (junk_4);
      x = y;
      junk_0 = junk_3;
      y = ((y) + (1));
      junk_0 = 781;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
