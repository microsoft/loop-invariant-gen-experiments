int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 1;
  int junk_2 = 0;
  int junk_3 = 3;
  int junk_4 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_2;
      x = y;
      junk_4 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 489;
      x = y;
      junk_4 = junk_4 - (227);
      y = ((y) + (1));
      junk_0 = junk_2 + (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
