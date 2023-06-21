int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 3;
  int junk_3 = 1;
  int junk_4 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_2 - (junk_1);
      x = y;
      junk_2 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 807 - (junk_3);
      x = y;
      junk_3 = junk_4 - (936);
      y = ((y) + (1));
      junk_4 = junk_1 + (826);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
