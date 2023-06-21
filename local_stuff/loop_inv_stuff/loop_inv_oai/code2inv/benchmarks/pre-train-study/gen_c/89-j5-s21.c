int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 9;
  int junk_3 = 4;
  int junk_4 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_2 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1 - (829);
      x = y;
      junk_1 = junk_1;
      y = ((y) + (1));
      junk_3 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
