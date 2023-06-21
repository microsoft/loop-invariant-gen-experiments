int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 8;
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
      junk_1 = junk_2 + (875);
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 106;
      x = y;
      junk_1 = junk_0;
      y = ((y) + (1));
      junk_1 = junk_2 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
