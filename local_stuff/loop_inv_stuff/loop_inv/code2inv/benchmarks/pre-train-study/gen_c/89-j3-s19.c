int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 6;
  int junk_2 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 827;
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1;
      x = y;
      junk_2 = junk_2;
      y = ((y) + (1));
      junk_2 = junk_2 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
