int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 9;
  int junk_2 = 8;
  int junk_3 = 5;
  int junk_4 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 602 + (325);
      x = y;
      junk_3 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_3;
      x = y;
      junk_3 = junk_3;
      y = ((y) + (1));
      junk_1 = junk_3;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
