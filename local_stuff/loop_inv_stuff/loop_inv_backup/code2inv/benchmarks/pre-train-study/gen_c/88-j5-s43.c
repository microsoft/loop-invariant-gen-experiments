int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 3;
  int junk_3 = 7;
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
      junk_4 = 294 - (junk_3);
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 763;
      x = y;
      junk_0 = 656;
      y = ((y) + (1));
      junk_3 = 86;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
