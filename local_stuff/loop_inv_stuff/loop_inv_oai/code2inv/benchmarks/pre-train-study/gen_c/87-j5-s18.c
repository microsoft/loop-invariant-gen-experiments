int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 6;
  int junk_3 = 3;
  int junk_4 = 6;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_0;
      x = y;
      junk_2 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 711;
      x = y;
      junk_1 = 992 + (49);
      y = ((y) + (1));
      junk_3 = 290 - (539);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
