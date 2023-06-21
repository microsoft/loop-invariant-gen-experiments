int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 5;
  int junk_2 = 9;
  int junk_3 = 7;
  int junk_4 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_0 - (154);
      x = y;
      junk_2 = 514;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 930;
      x = y;
      junk_3 = junk_1;
      y = ((y) + (1));
      junk_0 = junk_3 + (586);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
