int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 1;
  int junk_2 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 316 + (junk_1);
      x = y;
      junk_2 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 962;
      x = y;
      junk_0 = 52 - (503);
      y = ((y) + (1));
      junk_1 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
