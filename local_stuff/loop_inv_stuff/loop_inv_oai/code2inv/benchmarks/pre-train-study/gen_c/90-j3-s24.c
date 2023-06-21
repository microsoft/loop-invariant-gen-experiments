int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 7;
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
      junk_0 = 425;
      x = y;
      junk_2 = 983;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_0;
      x = y;
      junk_1 = 165 + (391);
      y = ((y) + (1));
      junk_1 = 647 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
