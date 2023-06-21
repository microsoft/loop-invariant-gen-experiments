int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 8;
  int junk_2 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 236;
      x = y;
      junk_0 = 780;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_1 - (junk_0);
      x = y;
      junk_2 = junk_2 - (junk_2);
      y = ((y) + (1));
      junk_1 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
