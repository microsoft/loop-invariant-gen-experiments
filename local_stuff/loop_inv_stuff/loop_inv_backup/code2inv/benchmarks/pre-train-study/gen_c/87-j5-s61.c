int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 2;
  int junk_3 = 8;
  int junk_4 = 1;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_4 - (junk_1);
      x = y;
      junk_2 = junk_4;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 684;
      x = y;
      junk_4 = junk_2 - (675);
      y = ((y) + (1));
      junk_4 = 699;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
