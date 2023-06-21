int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 6;
  int junk_2 = 3;
  int junk_3 = 6;
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
      junk_0 = 816 - (230);
      x = y;
      junk_0 = 737 + (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_2 + (junk_3);
      x = y;
      junk_4 = junk_3;
      y = ((y) + (1));
      junk_2 = 294 - (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
