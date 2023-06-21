int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 4;
  int junk_2 = 1;
  int junk_3 = 9;
  int junk_4 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_0;
      x = y;
      junk_0 = 950;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 433;
      x = y;
      junk_2 = junk_4;
      y = ((y) + (1));
      junk_1 = 889 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
