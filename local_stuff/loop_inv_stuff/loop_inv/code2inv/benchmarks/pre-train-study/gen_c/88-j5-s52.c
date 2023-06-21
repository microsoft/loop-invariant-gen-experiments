int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 8;
  int junk_2 = 1;
  int junk_3 = 1;
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
      junk_3 = junk_1 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_3;
      x = y;
      junk_2 = junk_1 - (582);
      y = ((y) + (1));
      junk_2 = 114 - (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
