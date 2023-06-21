int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 3;
  int junk_2 = 3;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 546 - (542);
      x = y;
      junk_2 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_2 - (junk_0);
      x = y;
      junk_1 = 907 + (junk_1);
      y = ((y) + (1));
      junk_2 = 879 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
