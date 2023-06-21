int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 0;
  int junk_4 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 728;
      x = y;
      junk_4 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 185 - (junk_2);
      x = y;
      junk_3 = 656;
      y = ((y) + (1));
      junk_4 = 103;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
