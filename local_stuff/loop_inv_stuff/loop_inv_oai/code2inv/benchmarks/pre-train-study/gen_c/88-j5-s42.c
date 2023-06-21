int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 1;
  int junk_2 = 3;
  int junk_3 = 2;
  int junk_4 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_4;
      x = y;
      junk_0 = junk_3 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 485 - (195);
      x = y;
      junk_1 = junk_1;
      y = ((y) + (1));
      junk_2 = junk_2 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
