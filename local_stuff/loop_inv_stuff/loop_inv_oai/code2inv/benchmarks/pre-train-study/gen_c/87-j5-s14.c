int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 4;
  int junk_3 = 1;
  int junk_4 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_2;
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_2;
      x = y;
      junk_3 = junk_1 + (401);
      y = ((y) + (1));
      junk_4 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
