int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 9;
  int junk_2 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1 + (425);
      x = y;
      junk_1 = 41;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_0;
      x = y;
      junk_1 = 502;
      y = ((y) + (1));
      junk_0 = 921;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
