int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 464;
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 686;
      x = y;
      junk_0 = 949;
      y = ((y) + (1));
      junk_0 = 896;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
