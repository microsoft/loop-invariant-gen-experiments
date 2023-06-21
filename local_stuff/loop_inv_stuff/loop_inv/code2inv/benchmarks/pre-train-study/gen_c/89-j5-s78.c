int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 1;
  int junk_2 = 3;
  int junk_3 = 0;
  int junk_4 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 310;
      x = y;
      junk_0 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 957;
      x = y;
      junk_0 = junk_4 - (junk_0);
      y = ((y) + (1));
      junk_3 = junk_1 + (34);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
