int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 4;
  int junk_2 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 510;
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 603;
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_0 = 335;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
