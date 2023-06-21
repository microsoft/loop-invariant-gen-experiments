int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 3;
  int junk_2 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 688;
      x = y;
      junk_1 = junk_0 + (443);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1;
      x = y;
      junk_0 = 945;
      y = ((y) + (1));
      junk_2 = 896;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
