int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 6;
  int junk_3 = 0;
  int junk_4 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_2 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_1 + (junk_2);
      x = y;
      junk_1 = 210;
      y = ((y) + (1));
      junk_0 = junk_4 - (991);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
