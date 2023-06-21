int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 5;
  int junk_2 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 465;
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 - (966);
      x = y;
      junk_1 = junk_0 - (junk_2);
      y = ((y) + (1));
      junk_2 = 818;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
