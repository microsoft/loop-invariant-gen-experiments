int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 3;
  int junk_2 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0 + (401);
      x = y;
      junk_2 = 859;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_1;
      x = y;
      junk_1 = junk_0 + (734);
      y = ((y) + (1));
      junk_1 = 718;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
