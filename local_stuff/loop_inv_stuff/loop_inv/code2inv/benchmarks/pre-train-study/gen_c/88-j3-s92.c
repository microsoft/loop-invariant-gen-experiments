int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 3;
  int junk_2 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 837 - (392);
      x = y;
      junk_0 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2 - (720);
      x = y;
      junk_0 = junk_1;
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
