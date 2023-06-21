int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 6;
  int junk_2 = 9;
  int junk_3 = 8;
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
      junk_3 = junk_0;
      x = y;
      junk_0 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_0 - (461);
      x = y;
      junk_3 = junk_2 - (junk_4);
      y = ((y) + (1));
      junk_2 = 368;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
