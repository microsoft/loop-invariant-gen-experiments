int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 0;
  int junk_2 = 0;
  int junk_3 = 1;
  int junk_4 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_1 + (638);
      x = y;
      junk_4 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 813;
      x = y;
      junk_2 = 999 - (junk_3);
      y = ((y) + (1));
      junk_1 = junk_0 + (287);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
