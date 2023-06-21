int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 2;
  int junk_2 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_1;
      x = y;
      junk_0 = 570 - (265);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0;
      x = y;
      junk_1 = 26;
      y = ((y) + (1));
      junk_0 = 63;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
