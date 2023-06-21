int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 2;
  int junk_3 = 7;
  int junk_4 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 426;
      x = y;
      junk_0 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 579 - (685);
      x = y;
      junk_3 = 207;
      y = ((y) + (1));
      junk_4 = 446;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
