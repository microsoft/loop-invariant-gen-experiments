int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 4;
  int junk_2 = 3;
  int junk_3 = 7;
  int junk_4 = 5;
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
      junk_3 = 82 + (25);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 114;
      x = y;
      junk_0 = junk_2;
      y = ((y) + (1));
      junk_3 = 831 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
