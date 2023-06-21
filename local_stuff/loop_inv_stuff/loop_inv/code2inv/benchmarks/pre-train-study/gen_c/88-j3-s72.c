int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 9;
  int junk_2 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 838;
      x = y;
      junk_1 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2;
      x = y;
      junk_0 = 928 - (854);
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
