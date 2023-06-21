int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 1;
  int junk_2 = 8;
  int junk_3 = 9;
  int junk_4 = 3;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 471;
      x = y;
      junk_0 = junk_3 - (502);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_4;
      x = y;
      junk_4 = junk_0;
      y = ((y) + (1));
      junk_2 = junk_1 - (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
