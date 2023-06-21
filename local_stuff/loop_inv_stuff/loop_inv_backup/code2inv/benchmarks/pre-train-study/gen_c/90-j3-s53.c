int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 3;
  int junk_2 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0;
      x = y;
      junk_2 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 24;
      x = y;
      junk_2 = 88;
      y = ((y) + (1));
      junk_1 = 597 - (46);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
