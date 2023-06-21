int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 1;
  int junk_3 = 8;
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
      junk_4 = 296 + (junk_0);
      x = y;
      junk_4 = 669 + (355);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 940;
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_3 = junk_4 - (821);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
