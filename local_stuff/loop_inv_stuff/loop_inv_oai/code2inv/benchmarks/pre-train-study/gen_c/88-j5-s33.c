int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 9;
  int junk_2 = 1;
  int junk_3 = 2;
  int junk_4 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = junk_4;
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 968;
      x = y;
      junk_1 = junk_0;
      y = ((y) + (1));
      junk_1 = junk_4 - (518);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
