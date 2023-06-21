int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 6;
  int junk_2 = 2;
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
      junk_2 = 106 - (960);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_2;
      x = y;
      junk_0 = 410;
      y = ((y) + (1));
      junk_0 = 996;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
