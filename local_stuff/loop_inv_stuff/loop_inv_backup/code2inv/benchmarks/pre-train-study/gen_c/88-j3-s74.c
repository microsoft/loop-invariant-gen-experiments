int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 3;
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
      junk_0 = 757;
      x = y;
      junk_0 = junk_0 - (892);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 + (309);
      x = y;
      junk_0 = 285;
      y = ((y) + (1));
      junk_0 = junk_0 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
