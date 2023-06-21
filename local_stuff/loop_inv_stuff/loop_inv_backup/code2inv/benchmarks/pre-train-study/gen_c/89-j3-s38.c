int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 6;
  int junk_2 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 280 + (junk_2);
      x = y;
      junk_0 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 878 + (705);
      x = y;
      junk_0 = 138;
      y = ((y) + (1));
      junk_0 = 594;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
