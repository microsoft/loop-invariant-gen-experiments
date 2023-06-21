int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 1;
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
      junk_1 = 940 - (junk_0);
      x = y;
      junk_2 = 331 - (815);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 180;
      x = y;
      junk_0 = junk_1;
      y = ((y) + (1));
      junk_0 = junk_2 - (425);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
