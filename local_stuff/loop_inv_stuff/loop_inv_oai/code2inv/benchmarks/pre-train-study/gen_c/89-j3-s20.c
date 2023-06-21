int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 7;
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
      junk_0 = junk_0;
      x = y;
      junk_2 = 888;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 81 + (junk_1);
      x = y;
      junk_2 = junk_1;
      y = ((y) + (1));
      junk_0 = junk_2 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
