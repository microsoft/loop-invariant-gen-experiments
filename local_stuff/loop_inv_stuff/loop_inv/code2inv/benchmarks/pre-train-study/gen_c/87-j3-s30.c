int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
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
      junk_1 = 149;
      x = y;
      junk_1 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_1;
      x = y;
      junk_0 = junk_1 + (781);
      y = ((y) + (1));
      junk_0 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
