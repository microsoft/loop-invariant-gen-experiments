int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 8;
  int junk_2 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_1 = junk_0 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2;
      x = y;
      junk_2 = junk_1;
      y = ((y) + (1));
      junk_0 = 414 + (473);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
