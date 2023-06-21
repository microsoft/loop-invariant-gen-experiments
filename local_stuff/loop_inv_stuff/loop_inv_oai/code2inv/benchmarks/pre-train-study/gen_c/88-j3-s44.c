int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 5;
  int junk_2 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1 + (451);
      x = y;
      junk_2 = 498 + (250);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_1;
      x = y;
      junk_1 = junk_1;
      y = ((y) + (1));
      junk_2 = junk_0 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
