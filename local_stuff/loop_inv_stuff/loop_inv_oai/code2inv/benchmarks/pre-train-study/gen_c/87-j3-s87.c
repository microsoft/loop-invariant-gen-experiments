int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 4;
  int junk_2 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0 + (728);
      x = y;
      junk_2 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 167;
      x = y;
      junk_0 = junk_1 + (357);
      y = ((y) + (1));
      junk_1 = 829;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
