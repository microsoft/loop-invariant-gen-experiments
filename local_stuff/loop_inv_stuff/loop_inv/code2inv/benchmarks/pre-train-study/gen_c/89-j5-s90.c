int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 9;
  int junk_2 = 3;
  int junk_3 = 2;
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
      junk_2 = 827;
      x = y;
      junk_2 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 891;
      x = y;
      junk_1 = 883 + (34);
      y = ((y) + (1));
      junk_2 = 789;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
