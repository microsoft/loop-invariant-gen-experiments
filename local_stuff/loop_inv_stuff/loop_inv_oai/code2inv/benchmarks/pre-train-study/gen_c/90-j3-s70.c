int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 5;
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
      junk_0 = junk_0 + (junk_1);
      x = y;
      junk_0 = 295 + (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 255;
      x = y;
      junk_0 = junk_2;
      y = ((y) + (1));
      junk_1 = 36;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
