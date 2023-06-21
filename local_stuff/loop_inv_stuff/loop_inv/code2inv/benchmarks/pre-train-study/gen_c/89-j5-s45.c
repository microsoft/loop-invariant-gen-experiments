int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 6;
  int junk_3 = 8;
  int junk_4 = 1;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 868 - (528);
      x = y;
      junk_2 = 610 - (229);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_2;
      x = y;
      junk_1 = 490;
      y = ((y) + (1));
      junk_2 = 857 + (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
