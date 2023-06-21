int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 8;
  int junk_2 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0;
      x = y;
      junk_1 = 870;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 508;
      x = y;
      junk_0 = 795 - (54);
      y = ((y) + (1));
      junk_1 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
