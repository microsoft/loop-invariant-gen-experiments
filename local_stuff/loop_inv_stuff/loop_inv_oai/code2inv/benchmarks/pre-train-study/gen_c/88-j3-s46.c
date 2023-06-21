int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 783 + (849);
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 292 - (junk_1);
      x = y;
      junk_0 = 974;
      y = ((y) + (1));
      junk_0 = 448 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
