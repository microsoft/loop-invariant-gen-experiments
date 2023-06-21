int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 3;
  int junk_2 = 5;
  int junk_3 = 2;
  int junk_4 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0;
      x = y;
      junk_4 = 266 - (645);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 - (261);
      x = y;
      junk_0 = 230;
      y = ((y) + (1));
      junk_1 = junk_3 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
