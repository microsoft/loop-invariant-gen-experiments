int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 1;
  int junk_2 = 1;
  int junk_3 = 3;
  int junk_4 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 262;
      x = y;
      junk_0 = 426 + (junk_4);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_2 + (397);
      x = y;
      junk_0 = junk_4;
      y = ((y) + (1));
      junk_2 = 457 + (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
