int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 0;
  int junk_3 = 7;
  int junk_4 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0 + (533);
      x = y;
      junk_2 = junk_3 - (279);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 432;
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_1 = 795;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
