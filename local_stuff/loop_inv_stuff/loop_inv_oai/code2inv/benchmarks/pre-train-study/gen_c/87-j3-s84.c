int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 4;
  int junk_2 = 1;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_0;
      x = y;
      junk_0 = 936;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 591;
      x = y;
      junk_0 = junk_1;
      y = ((y) + (1));
      junk_2 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
