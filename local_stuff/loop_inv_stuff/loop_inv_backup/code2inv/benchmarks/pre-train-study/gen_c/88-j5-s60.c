int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 7;
  int junk_2 = 6;
  int junk_3 = 1;
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
      junk_1 = 286;
      x = y;
      junk_2 = 380;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 423 + (713);
      x = y;
      junk_2 = 624;
      y = ((y) + (1));
      junk_3 = junk_4 + (427);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
