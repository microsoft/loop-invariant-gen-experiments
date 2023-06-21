int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 0;
  int junk_2 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 167 + (junk_0);
      x = y;
      junk_2 = 910;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 315;
      x = y;
      junk_0 = 268;
      y = ((y) + (1));
      junk_2 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
