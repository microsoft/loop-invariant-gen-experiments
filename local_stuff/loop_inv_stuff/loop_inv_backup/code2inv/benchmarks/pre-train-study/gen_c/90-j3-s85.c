int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0;
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 982;
      x = y;
      junk_0 = 883 - (junk_1);
      y = ((y) + (1));
      junk_0 = junk_1 + (268);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
