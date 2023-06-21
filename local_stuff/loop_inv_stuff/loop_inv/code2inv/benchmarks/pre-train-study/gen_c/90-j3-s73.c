int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 6;
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
      junk_1 = junk_0 + (414);
      x = y;
      junk_2 = 110 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 + (560);
      x = y;
      junk_1 = junk_0;
      y = ((y) + (1));
      junk_2 = junk_2 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
