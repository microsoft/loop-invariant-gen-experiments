int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 0;
  int junk_2 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_0 = 975;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2;
      x = y;
      junk_2 = 645 - (225);
      y = ((y) + (1));
      junk_1 = 973 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
