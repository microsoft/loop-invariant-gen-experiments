int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 9;
  int junk_3 = 9;
  int junk_4 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = junk_4 - (junk_0);
      x = y;
      junk_4 = 684;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_3 + (junk_2);
      x = y;
      junk_3 = junk_4;
      y = ((y) + (1));
      junk_4 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
