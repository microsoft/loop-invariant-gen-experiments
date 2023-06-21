int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 5;
  int junk_3 = 8;
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
      junk_3 = junk_3 - (junk_1);
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0 + (450);
      x = y;
      junk_0 = junk_3;
      y = ((y) + (1));
      junk_4 = 353;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
