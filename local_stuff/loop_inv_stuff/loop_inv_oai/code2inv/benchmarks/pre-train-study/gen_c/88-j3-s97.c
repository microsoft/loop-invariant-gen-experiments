int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 7;
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
      junk_0 = junk_1;
      x = y;
      junk_0 = 23;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2 + (junk_2);
      x = y;
      junk_0 = junk_1;
      y = ((y) + (1));
      junk_0 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
