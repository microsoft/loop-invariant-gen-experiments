int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 6;
  int junk_2 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0 - (junk_1);
      x = y;
      junk_2 = 512;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 909 - (junk_1);
      x = y;
      junk_2 = junk_0;
      y = ((y) + (1));
      junk_0 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
