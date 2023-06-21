int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 9;
  int junk_2 = 3;
  int junk_3 = 7;
  int junk_4 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1 + (128);
      x = y;
      junk_4 = junk_3 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 117 - (junk_2);
      x = y;
      junk_4 = 703 + (junk_2);
      y = ((y) + (1));
      junk_0 = junk_1 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
