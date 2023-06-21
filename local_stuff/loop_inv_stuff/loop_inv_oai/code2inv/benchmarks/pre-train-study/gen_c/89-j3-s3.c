int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 5;
  int junk_2 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 222 + (811);
      x = y;
      junk_2 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2 + (217);
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_1 = 429 + (936);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
