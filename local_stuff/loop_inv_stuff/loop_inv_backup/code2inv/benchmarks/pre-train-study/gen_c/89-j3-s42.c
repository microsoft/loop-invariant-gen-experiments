int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 4;
  int junk_2 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 42;
      x = y;
      junk_2 = 772;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2 - (junk_2);
      x = y;
      junk_2 = 595 + (423);
      y = ((y) + (1));
      junk_0 = 564 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
