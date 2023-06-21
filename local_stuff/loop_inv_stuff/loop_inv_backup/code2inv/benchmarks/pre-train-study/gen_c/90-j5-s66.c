int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 9;
  int junk_2 = 2;
  int junk_3 = 1;
  int junk_4 = 4;
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
      junk_4 = junk_0 + (810);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_2 - (530);
      x = y;
      junk_4 = 929;
      y = ((y) + (1));
      junk_0 = 92;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
