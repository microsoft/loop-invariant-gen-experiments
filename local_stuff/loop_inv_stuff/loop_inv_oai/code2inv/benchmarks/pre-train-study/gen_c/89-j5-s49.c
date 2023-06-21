int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 3;
  int junk_2 = 1;
  int junk_3 = 2;
  int junk_4 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 444 + (junk_2);
      x = y;
      junk_2 = 259;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_3 - (junk_3);
      x = y;
      junk_3 = junk_1 - (junk_3);
      y = ((y) + (1));
      junk_1 = junk_1 - (722);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
