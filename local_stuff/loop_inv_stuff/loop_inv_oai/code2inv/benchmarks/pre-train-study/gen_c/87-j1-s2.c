int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 820;
      x = y;
      junk_0 = 257;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 533;
      x = y;
      junk_0 = 232 + (junk_0);
      y = ((y) + (1));
      junk_0 = 931;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
