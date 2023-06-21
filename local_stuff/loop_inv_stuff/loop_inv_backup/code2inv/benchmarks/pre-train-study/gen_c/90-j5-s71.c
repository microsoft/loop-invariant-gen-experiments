int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 6;
  int junk_2 = 7;
  int junk_3 = 1;
  int junk_4 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_1;
      x = y;
      junk_2 = 865 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0;
      x = y;
      junk_4 = 990;
      y = ((y) + (1));
      junk_3 = 611;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
