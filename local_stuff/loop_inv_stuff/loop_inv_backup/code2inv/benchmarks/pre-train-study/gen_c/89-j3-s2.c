int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 4;
  int junk_2 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 716;
      x = y;
      junk_0 = 140 + (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 736;
      x = y;
      junk_1 = 206;
      y = ((y) + (1));
      junk_2 = junk_1 - (199);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
