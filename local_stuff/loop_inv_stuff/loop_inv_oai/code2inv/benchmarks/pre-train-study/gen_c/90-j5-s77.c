int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 3;
  int junk_2 = 3;
  int junk_3 = 7;
  int junk_4 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 327;
      x = y;
      junk_3 = junk_0 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_4 - (junk_0);
      x = y;
      junk_2 = junk_1 - (junk_4);
      y = ((y) + (1));
      junk_2 = 181 + (junk_3);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
