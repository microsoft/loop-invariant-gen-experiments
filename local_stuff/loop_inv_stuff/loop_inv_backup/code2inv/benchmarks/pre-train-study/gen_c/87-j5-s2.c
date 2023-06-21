int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 8;
  int junk_2 = 6;
  int junk_3 = 4;
  int junk_4 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 257;
      x = y;
      junk_2 = 533;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 232 + (junk_2);
      x = y;
      junk_4 = 931;
      y = ((y) + (1));
      junk_4 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
