int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 6;
  int junk_2 = 7;
  int junk_3 = 8;
  int junk_4 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 644;
      x = y;
      junk_3 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_4;
      x = y;
      junk_4 = junk_4;
      y = ((y) + (1));
      junk_4 = junk_3 + (879);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
