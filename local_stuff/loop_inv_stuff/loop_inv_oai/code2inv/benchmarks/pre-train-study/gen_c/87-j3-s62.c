int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 9;
  int junk_2 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 790 + (junk_1);
      x = y;
      junk_0 = 823;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_2;
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_1 = junk_1 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
