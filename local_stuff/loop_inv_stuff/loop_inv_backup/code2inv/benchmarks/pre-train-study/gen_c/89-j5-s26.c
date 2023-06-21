int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 7;
  int junk_2 = 9;
  int junk_3 = 2;
  int junk_4 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_0 = junk_0 + (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_4;
      x = y;
      junk_4 = junk_3 - (942);
      y = ((y) + (1));
      junk_1 = 967 + (381);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
