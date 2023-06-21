int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 6;
  int junk_2 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_0 = junk_0 + (320);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 541;
      x = y;
      junk_1 = 637;
      y = ((y) + (1));
      junk_2 = 81;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
