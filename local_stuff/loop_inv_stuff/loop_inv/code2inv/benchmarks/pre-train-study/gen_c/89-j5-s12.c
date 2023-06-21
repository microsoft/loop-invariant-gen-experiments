int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 5;
  int junk_3 = 8;
  int junk_4 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 41;
      x = y;
      junk_3 = 109;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_3 + (943);
      x = y;
      junk_0 = junk_2 - (459);
      y = ((y) + (1));
      junk_0 = junk_1 + (143);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
