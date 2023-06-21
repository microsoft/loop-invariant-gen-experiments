int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 8;
  int junk_2 = 6;
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
      junk_2 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 698 + (176);
      x = y;
      junk_1 = 279 + (407);
      y = ((y) + (1));
      junk_0 = junk_2 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
