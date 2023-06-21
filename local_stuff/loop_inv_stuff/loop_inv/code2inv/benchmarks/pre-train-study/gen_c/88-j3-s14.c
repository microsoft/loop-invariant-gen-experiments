int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 7;
  int junk_2 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 467;
      x = y;
      junk_0 = junk_1 + (216);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 174;
      x = y;
      junk_2 = 624;
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
