int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 9;
  int junk_2 = 7;
  int junk_3 = 6;
  int junk_4 = 1;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = 981;
      x = y;
      junk_3 = 419;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_2 + (626);
      x = y;
      junk_2 = junk_4;
      y = ((y) + (1));
      junk_2 = 732 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
