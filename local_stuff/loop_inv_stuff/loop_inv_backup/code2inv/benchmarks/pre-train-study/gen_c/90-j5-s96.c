int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 3;
  int junk_4 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1 - (451);
      x = y;
      junk_2 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 647;
      x = y;
      junk_4 = 462 - (junk_0);
      y = ((y) + (1));
      junk_4 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
