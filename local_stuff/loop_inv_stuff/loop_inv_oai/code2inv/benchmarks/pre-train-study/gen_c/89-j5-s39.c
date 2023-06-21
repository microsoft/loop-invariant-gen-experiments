int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 1;
  int junk_3 = 4;
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
      junk_3 = 498;
      x = y;
      junk_0 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 331;
      x = y;
      junk_0 = junk_3;
      y = ((y) + (1));
      junk_2 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
