int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 9;
  int junk_2 = 1;
  int junk_3 = 4;
  int junk_4 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 746;
      x = y;
      junk_0 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_1 + (32);
      x = y;
      junk_0 = junk_2;
      y = ((y) + (1));
      junk_3 = 911 + (746);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
