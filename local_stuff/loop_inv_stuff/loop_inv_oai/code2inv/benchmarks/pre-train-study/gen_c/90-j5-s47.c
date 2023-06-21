int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 8;
  int junk_3 = 3;
  int junk_4 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = junk_3;
      x = y;
      junk_3 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_2 + (615);
      x = y;
      junk_4 = 35;
      y = ((y) + (1));
      junk_0 = junk_1 + (38);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
