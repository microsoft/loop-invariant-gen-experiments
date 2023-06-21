int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 665;
      x = y;
      junk_2 = 895 + (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 461;
      x = y;
      junk_0 = 16 + (junk_1);
      y = ((y) + (1));
      junk_0 = 285 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
