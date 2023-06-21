int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 4;
  int junk_2 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0;
      x = y;
      junk_1 = 49 + (junk_1);
      y = ((y) + (1));
      junk_1 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
