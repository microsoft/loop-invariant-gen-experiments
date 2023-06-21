int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
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
      junk_2 = 629;
      x = y;
      junk_2 = junk_1 - (410);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0;
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_2 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
