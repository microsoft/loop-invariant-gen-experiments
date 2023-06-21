int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 4;
  int junk_2 = 1;
  int junk_3 = 3;
  int junk_4 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 657;
      x = y;
      junk_0 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 808;
      x = y;
      junk_4 = junk_2;
      y = ((y) + (1));
      junk_3 = junk_4 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
