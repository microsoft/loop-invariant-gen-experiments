int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 776;
      x = y;
      junk_0 = junk_0 + (229);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 518;
      x = y;
      junk_1 = 524;
      y = ((y) + (1));
      junk_2 = junk_0 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
