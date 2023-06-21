int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 9;
  int junk_2 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 842;
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 309;
      x = y;
      junk_0 = junk_1 + (324);
      y = ((y) + (1));
      junk_1 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
