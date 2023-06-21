int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 524;
      x = y;
      junk_0 = 198;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 - (256);
      x = y;
      junk_0 = 57 - (106);
      y = ((y) + (1));
      junk_0 = junk_0 - (828);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
