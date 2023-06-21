int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 7;
  int junk_2 = 7;
  int junk_3 = 7;
  int junk_4 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = 376 + (junk_2);
      x = y;
      junk_1 = 455 - (165);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1;
      x = y;
      junk_2 = junk_3;
      y = ((y) + (1));
      junk_2 = junk_3 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
