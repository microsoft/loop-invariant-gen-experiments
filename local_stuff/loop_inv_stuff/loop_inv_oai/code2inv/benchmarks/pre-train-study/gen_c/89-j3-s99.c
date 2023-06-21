int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 9;
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
      junk_1 = 415 + (184);
      x = y;
      junk_2 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1 - (junk_0);
      x = y;
      junk_0 = 679 - (junk_0);
      y = ((y) + (1));
      junk_2 = 534;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
