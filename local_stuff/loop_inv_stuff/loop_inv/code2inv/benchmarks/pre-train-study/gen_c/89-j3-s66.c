int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 8;
  int junk_2 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0;
      x = y;
      junk_0 = 9;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_2 - (294);
      x = y;
      junk_2 = 110 + (244);
      y = ((y) + (1));
      junk_1 = 341 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
