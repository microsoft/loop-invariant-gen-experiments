int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_2;
      x = y;
      junk_1 = junk_2 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_2;
      x = y;
      junk_1 = 710;
      y = ((y) + (1));
      junk_2 = 518 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
