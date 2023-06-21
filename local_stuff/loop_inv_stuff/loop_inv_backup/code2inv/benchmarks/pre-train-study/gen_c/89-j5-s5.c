int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 7;
  int junk_3 = 6;
  int junk_4 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 797;
      x = y;
      junk_2 = junk_3 + (627);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 613;
      x = y;
      junk_0 = junk_3;
      y = ((y) + (1));
      junk_0 = junk_1 + (821);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
