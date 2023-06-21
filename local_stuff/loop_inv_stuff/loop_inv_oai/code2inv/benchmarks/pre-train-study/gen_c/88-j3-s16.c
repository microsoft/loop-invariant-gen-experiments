int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 3;
  int junk_2 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_1 = 230 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 684;
      x = y;
      junk_0 = junk_1 - (junk_0);
      y = ((y) + (1));
      junk_2 = junk_2 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
